{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Main (main) where

import Control.Monad
import Copilot.Compile.C99
import Copilot.Theorem.Prover.SMT
import Language.Copilot
import Prelude qualified as P

fanController :: Stream Word8 -> Stream Bool
fanController tmp = fan
  where
    th = 28 + mux fan (-1) 1
    fan = [False] ++ tmp >= th

spec :: Spec
spec = do
  let tmpSimInput = P.cycle [26, 27, 28, 29, 30, 29, 28, 27]
      tmp = externW8 "tmp" (Just tmpSimInput)
      fan = fanController tmp
  observer "tmp" tmp
  trigger "fan" true [arg $ fanController tmp]

  let theoremInd_ a b = void $ theorem a (forall b) (kInduction def z3)

  -- If tmp has always been less than 27, the fan must always have been off.
  theoremInd_ "Safety: keep turn off (1)" do
    alwaysBeen (tmp < 27) ==> not (eventuallyPrev fan)

  -- If tmp has always been more than 28, the fan must always have been on except the 1st iteration.
  theoremInd_ "Safety: keep turn on (1)" do
    alwaysBeen (tmp > 28) ==> not (eventuallyPrev (not fan)) `since` previous (not fan)

  let increasing s = s > ([minBound] ++ s)
      decreasing s = s < ([maxBound] ++ s)

  -- If tmp has been increasing monotonically, the fan must always have been on after the time in the past when fan became on.
  theoremInd_ "Safety: keep turn on (2)" do
    eventuallyPrev (alwaysBeen $ increasing tmp) ==> not (eventuallyPrev (not fan)) `since` fan

  -- If tmp has been decreasing monotonically, the fan must always have been off after the time in the past when fan became off.
  theoremInd_ "Safety: keep turn off (2)" do
    eventuallyPrev (alwaysBeen $ decreasing tmp) ==> not (eventuallyPrev fan) `since` not fan

  -- Really?
  theoremInd_ "Liveness: eventually on" do
    eventuallyPrev (alwaysBeen $ increasing tmp) ==> eventuallyPrev fan `since` previous (not fan)

  -- Really?
  theoremInd_ "Liveness: eventually off" do
    eventuallyPrev (alwaysBeen $ decreasing tmp) ==> eventuallyPrev (not fan)

  let -- 28, 29, 28, 29, ...
      oscillation1 = [28 :: Word8, 29] ++ oscillation1
      -- 27, 26, 27, 26, ...
      oscillation2 = [27 :: Word8, 26] ++ oscillation2

  theoremInd_ "Safety: hysteresis control 1" do
    (tmp == oscillation1) ==> alwaysBeen fan `since` fan `since` not fan

  theoremInd_ "Safety: hysteresis control 2" do
    (tmp == oscillation2) ==> alwaysBeen (not fan) `since` not fan `since` fan

main :: IO ()
main = do
  defaultMain
    (compileWith mkDefaultCSettings {cSettingsOutputDirectory = "out"})
    spec
