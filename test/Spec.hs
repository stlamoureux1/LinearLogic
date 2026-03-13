module Main where

import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import LinType
import Sigma3
import Test.Hspec
import Test.QuickCheck

main :: IO ()
main = hspec $ do
  describe "(id1) test 1" $ do
    let nlCxt = Set.empty
        lCxt = Map.fromList [(Atom 0, 0)]
        evalCxt = EvalCxt {nlCxt = nlCxt, lCxt = lCxt}
        tm = Perp (Atom 0)
        resTree = evalState (id1 Dn [tm]) evalCxt
    it "" $ do
      resTree `shouldBe` IdTerminal1

  describe "(id1) test 2" $ do
    let nlCxt = Set.empty
        lCxt = Map.fromList [(Atom 0, 1), (Atom 1, 1), (Perp (Atom 1), 1)]
        evalCxt = EvalCxt {nlCxt = nlCxt, lCxt = lCxt}
        tm = Perp (Atom 0)
        (resTree, resCxt) = runState (id1 Dn [tm]) evalCxt
    it "" $ do
      resTree `shouldBe` IdRule1 (Decision1 IdTerminal1)
      resCxt
        `shouldBe` EvalCxt
          { nlCxt = Set.empty,
            lCxt = Map.empty
          }

  describe "(with) test 1" $ do
    let nlCxt = Set.empty
        lCxt = Map.fromList [(Atom 0, 1), (Atom 1, 1)]
        evalCxt = EvalCxt {nlCxt = nlCxt, lCxt = lCxt}
        tm = With (Perp (Atom 0)) (Perp (Atom 1))
        (resTree, resCxt) = runState (with Up [tm]) evalCxt
    it "" $ do
      resTree
        `shouldBe` WithRule
          (ReactionUp (Decision1 IdTerminal1))
          (ReactionUp (Decision1 IdTerminal1))
      resCxt `shouldBe` evalCxt

  describe "(tens) test 1" $ do
    let nlCxt = Set.empty
        lCxt = Map.fromList [(Atom 0, 1), (Atom 1, 1)]
        evalCxt = EvalCxt {nlCxt = nlCxt, lCxt = lCxt}
        tm = Tens (Perp (Atom 0)) (Perp (Atom 1))
        (resTree, resCxt) = runState (tens Dn [tm]) evalCxt
    it "" $ do
      resTree `shouldBe` TensRule IdTerminal1 IdTerminal1
      resCxt
        `shouldBe` EvalCxt
          { nlCxt = Set.empty,
            lCxt = Map.empty
          }

  describe "(par) test 1" $ do
    let nlCxt = Set.empty
        lCxt = Map.fromList [(Atom 0, 1), (Atom 1, 1)]
        evalCxt = EvalCxt {nlCxt = nlCxt, lCxt = lCxt}
        tm = Par (Perp (Atom 0)) (Perp (Atom 1))
        (resTree, resCxt) = runState (par Up [tm]) evalCxt
    it "" $ do
      resTree
        `shouldBe` ParRule
          (ReactionUp (ReactionUp (Decision1 (IdRule1 (Decision1 IdTerminal1)))))
      resCxt
        `shouldBe` EvalCxt
          { nlCxt = Set.empty,
            lCxt = Map.empty
          }
