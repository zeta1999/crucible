{-# Language GADTs, DataKinds, TypeOperators #-}
module Sim where

import Control.Lens((^.))
import Control.Monad.Reader
import Control.Monad.Identity
import Data.Parameterized.TraversableFC
import qualified Data.Parameterized.Context as Ctx

import Lang.Crucible.Backend
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.CallFrame
import Lang.Crucible.Simulator.EvalStmt
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension

import What4.Interface
import What4.Partial


-- | Various pices of data we need for the translation.
data TransInfo sym blocks = TransInfo
  { iBlockArgs  :: Ctx.Assignment (RegMap sym) blocks
  , iVerbosity  :: Int
  }

getBlockRegs :: TransInfo sym blocks -> BlockID blocks ctx -> RegMap sym ctx
getBlockRegs ti b = iBlockArgs ti Ctx.! blockIDIndex b


-- | Generate a bunch of variables for the inputs of the given block.
freshBlockArgs :: IsSymExprBuilder sym =>
  sym -> Block ext blocks ret ctx -> IO (RegMap sym ctx)
freshBlockArgs sym b = RegMap <$> traverseFC (newReg sym) (blockInputs b)

-- | Generate a variable of the given type.
-- Raises an expception of the given type does not support vairables.
newReg :: IsSymExprBuilder sym => sym -> TypeRepr tp -> IO (RegEntry sym tp)
newReg sym tp =
  case asBaseType tp of
    AsBaseType bt ->
      do expr <- freshConstant sym emptySymbol bt
         pure RegEntry { regType = tp, regValue = expr }
    NotBaseType -> fail "Not a base type." -- XXX: better error


data Next sym blocks = Next
  { nextCases   :: [(RegValue sym BoolType, ResolvedJump sym blocks)]
    -- ^ Try these one at a time

  , nextDefault :: Maybe (ResolvedJump sym blocks)
    -- ^ Go here if all of the above are false.
    -- Abort if this is nothing.
  }

nextJump :: ResolvedJump sym blocks -> Next sym blocks
nextJump l = Next { nextCases = [], nextDefault = Just l }

nextBr :: RegValue sym BoolType ->
          ResolvedJump sym blocks ->
          ResolvedJump sym blocks ->
          Next sym blocks
nextBr p t e = Next { nextCases = [(p,t)], nextDefault = Just e }



whatNext ::
  IsSymInterface sym =>
  TermStmt blocks r ctx ->
  CrucibleState p sym ext rtp blocks r ctx ->
  Next sym blocks

whatNext term st =
  runIdentity $ flip runReaderT st $
  case term of

    Jump tgt -> nextJump <$> evalJumpTarget tgt

    Br c t e -> nextBr <$> evalReg c <*> evalJumpTarget t <*> evalJumpTarget e

    MaybeBranch tp e j n ->
      do res <- evalReg e
         case res of
           Unassigned -> nextJump <$> evalJumpTarget n
           PE p v     -> nextBr p <$> evalSwitchTarget j (RegEntry tp v)
                                  <*> evalJumpTarget n

    VariantElim ctx e cases ->
        do vs <- evalReg e
           opts <-
             Ctx.traverseAndCollect (\i tp ->
                case vs Ctx.! i of
                  VB Unassigned -> return []
                  VB (PE p v) ->
                    do jmp <- evalSwitchTarget (cases Ctx.! i) (RegEntry tp v)
                       return [(p,jmp)])
              ctx
           pure Next { nextCases = opts, nextDefault = Nothing }

simBlock ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  TransInfo sym blocks ->
  SimContext p sym ext ->
  SymGlobalState sym ->
  CFG ext blocks init ret ->
  BlockID blocks args ->
  IO (Next sym blocks)
simBlock ti ctxt glob cfg bid =
  do let args  = getBlockRegs ti bid
         frame = MF (mkBlockFrame cfg bid (emptyCFGPostdomInfo blockNum) args)
         st0   = SimState
                   { _stateContext = ctxt
                   , _abortHandler = defaultAbortHandler
                   , _stateTree    = singletonTree (GlobalPair frame glob)
                   }
     evalBlockBody (iVerbosity ti) (block ^. blockStmts) st0
  where
  block      = getBlock bid (cfgBlockMap cfg)
  blockNum   = Ctx.size (cfgBlockMap cfg)


evalBlockBody ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Verbosity -} ->
  StmtSeq ext blocks ret args ->
  CrucibleState p sym ext rtp blocks ret args ->
  IO (Next sym blocks)
evalBlockBody verb stmts st =
  case stmts of
    ConsStmt pl stmt rest ->
      do setCurrentProgramLoc sym pl
         next <- runReaderT (stepStmt' verb stmt rest) st
         case next of
           LocalStep st1 -> evalBlockBody verb rest st1
           CallFun f args t next ->
             do st1 <- runFun f args (ReturnToCrucible t next) st
                evalBlockBody verb next st1

    TermStmt pl t ->
      do setCurrentProgramLoc sym pl
         pure (whatNext t st)

  where
  sym = st ^. stateContext . ctxSymInterface


runFun :: FnVal sym args ret ->
          RegMap sym args ->
          ReturnHandler ret p sym ext rtp (CrucibleLang blocks r) ('Just ctx) ->
          CrucibleState p sym ext rtp blocks r ctx ->
          IO (CrucibleState p sym ext rtp blocks r (ctx ::> ret))
runFun f as h s =
  do exec <- runReaderT (callFunction f as h) s




