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

  theoremInd_ "Liveness: eventually on" do
    tmp >= 29 ==> eventuallyPrev fan `since` previous (not fan)

  theoremInd_ "Liveness: eventually off" do
    tmp < 27 ==> eventuallyPrev (not fan)

  theoremInd_ "Safety: keep turning off" do
    alwaysBeen (tmp < 27) ==> not (eventuallyPrev fan)

  theoremInd_ "Safety: keep turning on" do
    alwaysBeen (tmp >= 29) ==> not (eventuallyPrev (not fan)) `since` previous (not fan)

  let -- 28, 29, 28, 29, ...
      oscillation1 = [28 :: Word8, 29] ++ oscillation1
      -- 27, 26, 27, 26, ...
      oscillation2 = [27 :: Word8, 26] ++ oscillation2

  theoremInd_ "Safety: hysteresis control 1" do
    (tmp == oscillation1) ==> alwaysBeen fan `since` fan

  theoremInd_ "Safety: hysteresis control 2" do
    (tmp == oscillation2) ==> alwaysBeen (not fan) `since` not fan

main :: IO ()
main = do
  defaultMain
    (compileWith mkDefaultCSettings {cSettingsOutputDirectory = "out"})
    spec
