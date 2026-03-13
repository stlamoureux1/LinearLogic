module Sigma3 where

-- Andreoli (1992)'s Sigma_3 sequent calculus

import Control.Applicative
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import LinType

type NonLinearCxt = Set.Set LinType

type LinearCxt = Map.Map LinType Int

data Condition = Up | Dn deriving (Eq, Show)

data EvalCxt = EvalCxt
  { nlCxt :: NonLinearCxt,
    lCxt :: LinearCxt
  }
  deriving (Eq, Show)

type EvalState = State EvalCxt ProofTree

-- NOTE: In order to have the tensor rule evaluate efficiently,
-- we have to send the current context to the left-hand-side evaluation,
-- remove any matches from the linear context, and pass the result
-- evaluation context to the check for the right-hand-side.
-- BUT, that means we need a recursive version of each identity rule
-- so that we can look up a linear match and proceed with evaluation
-- This differs from Andreoli's formulation, which enforces the linear
-- id rule only when the linear context contains exactly one match for a
-- negative atomic goal. Hence, I distinguish terminal nodes from
-- intermediate nodes that result from applying identity rules.
--
-- Note also that I use a FailNode flag value instead of a Maybe monad
-- to track the point at which a search fails.

data ProofTree
  = IdTerminal1
  | IdTerminal2
  | IdRule1 ProofTree
  | IdRule2 ProofTree
  | Decision1 ProofTree
  | Decision2 ProofTree
  | ReactionDown ProofTree
  | ReactionUp ProofTree
  | BottomRule ProofTree
  | TopRule
  | OneRule
  | OfCourseRule ProofTree
  | WhyNotRule ProofTree
  | TensRule ProofTree ProofTree
  | ParRule ProofTree
  | PlusRuleLeft ProofTree
  | PlusRuleRight ProofTree
  | WithRule ProofTree ProofTree
  | FailNode
  deriving (Eq, Show)

-- helper functions for evaluating the identity cases
removeInstance :: LinType -> LinearCxt -> LinearCxt
removeInstance t lCxt
  | Map.lookup t lCxt == Just 1 = Map.delete t lCxt
  | otherwise = Map.adjust (subtract 1) t lCxt

-- The ID rules serve the function of the one 'Axiom' rule of linear logic.
-- Note that the focused calculus breaks all expressions down into their
-- atomic constituents. Both rules apply under the 'down' condition.

-- Id1 applies when we have a linear match, i.e. one 'input' corresponding
-- exactly to one 'output'.
-- It updates the state by removing one instance of the matched value.
id1 :: Condition -> [LinType] -> EvalState
id1 Dn [f] = do
  EvalCxt {nlCxt, lCxt} <- get
  if isAtomic f
    then do
      let newLCxt = removeInstance (dual f) lCxt
      put EvalCxt {nlCxt = nlCxt, lCxt = newLCxt}
      if Map.null newLCxt
        then return IdTerminal1
        else do
          -- not sure if this actually works
          -- the idea is to continue the search
          -- to exhaust the atomic exprs, this drives
          -- us into the decision rules, which departs
          -- from Andreoli
          evalResult <- eval Up []
          case evalResult of
            FailNode -> do
              return IdTerminal1
            _ -> return $ IdRule1 evalResult
    else return FailNode
id1 _ _ = return FailNode

-- Id2 checks for a match in the non-linear context.
id2 :: Condition -> [LinType] -> EvalState
id2 Dn [f] = do
  EvalCxt {nlCxt, lCxt} <- get
  if isAtomic f && Set.member (dual f) nlCxt && Map.null lCxt
    then return IdTerminal2
    else return FailNode
id2 _ _ = return FailNode

-- Reaction rules
-- These could be combined to one function, pattern-matched on the Condition,
-- but I'm leaving them separate so that the set of functions is in
-- one-to-one correspondence with Andreoli's rules
reactionUp :: Condition -> [LinType] -> EvalState
reactionUp Up (f : ts) = do
  EvalCxt {nlCxt, lCxt} <- get
  if not (isAsync f)
    then do
      put EvalCxt {nlCxt, lCxt = Map.insertWith (+) f 1 lCxt}
      evalResult <- eval Up ts
      return $ ReactionUp evalResult
    else return FailNode
reactionUp _ _ = return FailNode

reactionDn :: Condition -> [LinType] -> EvalState
reactionDn Dn [f] = do
  if not $ isSync f && not (isPerp f && isAtom f)
    then do
      evalResult <- eval Up [f]
      return $ ReactionDown evalResult
    else return FailNode
reactionDn _ _ = return FailNode

-- Decision rules

-- helper fns
chooseNonLinear' :: [LinType] -> Maybe LinType
chooseNonLinear' [] = Nothing
chooseNonLinear' (t : ts)
  | not $ isAtom t = Just t
  | otherwise = chooseNonLinear' ts

chooseNonLinear = chooseNonLinear' . Set.toList

chooseLinear' :: [(LinType, Int)] -> Maybe LinType
chooseLinear' [] = Nothing
chooseLinear' ((t, n) : ts)
  | not $ isAtom t = Just t
  | otherwise = chooseLinear' ts

chooseLinear = chooseLinear' . Map.toList

decision1 :: Condition -> [LinType] -> EvalState
decision1 Up [] = do
  EvalCxt {nlCxt, lCxt} <- get
  let choice = chooseLinear lCxt
  case choice of
    Just f -> do
      let newLCxt = removeInstance f lCxt
      put EvalCxt {nlCxt, lCxt = newLCxt}
      evalResult <- eval Dn [f]
      return $ Decision1 evalResult
    Nothing -> decision2 Up []

decision2 :: Condition -> [LinType] -> EvalState
decision2 Up [] = do
  EvalCxt {nlCxt, lCxt} <- get
  let choice = chooseNonLinear nlCxt
  case choice of
    Just f -> do
      evalResult <- eval Dn [f]
      return $ Decision2 evalResult
    Nothing -> return FailNode
decision2 _ _ = return FailNode

-- Rules for Logical Connectives

-- The rules for Top and One are the other kinds of terminating conditions,
-- besides the identity rules.
top :: Condition -> [LinType] -> EvalState
top Up (Top : ts) = return TopRule
top _ _ = return FailNode

one :: Condition -> [LinType] -> EvalState
one Up [One] = do
  EvalCxt {nlCxt, lCxt} <- get
  if Map.null lCxt
    then return OneRule
    else return FailNode
one _ _ = return FailNode

bottom :: Condition -> [LinType] -> EvalState
bottom Up (Bottom : ts) = do
  evalResult <- eval Up ts
  return $ BottomRule evalResult
bottom _ _ = return FailNode

-- Binary Connectives
par :: Condition -> [LinType] -> EvalState
par Up (Par f g : ts) = do
  evalResult <- eval Up (f : g : ts)
  return $ ParRule evalResult
par _ _ = return FailNode

with :: Condition -> [LinType] -> EvalState
with Up (With f g : ts) = do
  evalCxt <- get
  evalResultLeft <- eval Up (f : ts)
  put evalCxt
  evalResultRight <- eval Up (g : ts)
  -- TODO: Verify that it makes sense to restore the state
  -- from before evaluating both branches
  put evalCxt
  return $ WithRule evalResultLeft evalResultRight
with _ _ = return FailNode

tens :: Condition -> [LinType] -> EvalState
tens Dn [Tens f g] = do
  resultLeft <- eval Dn [f]
  resultRight <- eval Dn [g]
  return $ TensRule resultLeft resultRight
tens _ _ = return FailNode

plus :: Condition -> [LinType] -> EvalState
plus Dn [Plus f g] = do
  evalCxt <- get
  evalTreeLeft <- eval Dn [f]
  if evalTreeLeft == FailNode
    then do
      put evalCxt
      evalTreeRight <- eval Dn [g]
      if evalTreeRight == FailNode
        then return FailNode
        else return $ PlusRuleRight evalTreeRight
    else return $ PlusRuleLeft evalTreeLeft
plus _ _ = return FailNode

-- Exponentials
whyNot :: Condition -> [LinType] -> EvalState
whyNot Up (WhyNot f : ts) = do
  EvalCxt {nlCxt, lCxt} <- get
  let newNLCxt = Set.insert f nlCxt
  put EvalCxt {nlCxt = newNLCxt, lCxt}
  evalResult <- eval Up ts
  return $ WhyNotRule evalResult
whyNot _ _ = return FailNode

ofCourse :: Condition -> [LinType] -> EvalState
ofCourse Dn [OfCourse f] = do
  EvalCxt {nlCxt, lCxt} <- get
  if Map.null lCxt
    then do
      evalResult <- eval Up [f]
      return $ OfCourseRule evalResult
    else return FailNode
ofCourse _ _ = return FailNode

-- TODO: Figure a better way of dispatching
-- Originally tried Data.Data to pattern match
-- on constructores themselves into a look-up table
-- but it seemed less perspicuous and equally verbose.
eval :: Condition -> [LinType] -> EvalState
eval Dn ts = do
  case ts of
    [One] -> one Dn ts
    (Tens f g : tts) -> tens Dn ts
    [Plus f g] -> plus Dn ts
    [OfCourse f] -> ofCourse Dn ts
    [f] -> if isAtom f || isPerp f then id1 Dn ts else reactionDn Dn ts
    _ -> return FailNode
eval Up ts = do
  case ts of
    (Bottom : tts) -> bottom Up ts
    (Par f g : tts) -> par Up ts
    (Top : tts) -> top Up ts
    (With f g : tts) -> with Up ts
    (WhyNot f : tts) -> whyNot Up ts
    [] -> decision1 Up ts
    (f : tts) ->
      if not (isAsync f)
        then reactionUp Up ts
        else return FailNode
