module Sim where

import Data.Parameterized.TraversableFC

import Lang.Crucible.Simulator
import Lang.Crucible.CFG.Core
import What4.Interface



-- | Generate a bunch of variables for the inputs of the given block.
freshBlockArgs :: IsSymExprBuilder sym =>
  Block ext blocks ret ctx -> sym -> IO (RegMap sym ctx)
freshBlockArgs b sym = RegMap <$> traverseFC (newReg sym) (blockInputs b)

-- | Generate a variable of the given type.
-- Raises an expception of the given type does not support vairables.
newReg :: IsSymExprBuilder sym => sym -> TypeRepr tp -> IO (RegEntry sym tp)
newReg sym tp =
  case asBaseType tp of
    AsBaseType bt ->
      do expr <- freshConstant sym emptySymbol bt
         pure RegEntry { regType = tp, regValue = expr }
    NotBaseType -> fail "Not a base type." -- XXX: better error





