------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Value
-- Description      : Representation of values in the LLVM memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.LLVM.MemModel.Value
  ( -- * LLVM Value representation
    LLVMVal(..)
  , FloatSize(..)
  , Field
  , ptrToPtrVal
  , zeroInt

  , Pred'(..)
  , pred'
  , PartLLVMVal(..)
  , partValPreds
  , llvmValStorableType
  , bvConcatPartLLVMVal
  , bvToFloatPartLLVMVal
  , bvToDoublePartLLVMVal
  , bvToX86_FP80PartLLVMVal
  , consArrayPartLLVMVal
  , appendArrayPartLLVMVal
  , mkArrayPartLLVMVal
  , mkStructPartLLVMVal
  , selectLowBvPartLLVMVal
  , selectHighBvPartLLVMVal
  , arrayEltPartLLVMVal
  , fieldValPartLLVMVal
  , muxLLVMVal
  ) where

import           Control.Lens
import           Control.Monad.Trans.Except
import           Control.Monad.State.Strict
import           Data.List (intersperse)

import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Semigroup ( (<>) )
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Vector( Vector )
import qualified Data.Vector as V
import           Data.Word (Word64)

import           What4.Interface
import           What4.InterpretedFloatingPoint

import           Lang.Crucible.Backend
import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.Pointer

data FloatSize (fi :: FloatInfo) where
  SingleSize :: FloatSize SingleFloat
  DoubleSize :: FloatSize DoubleFloat
  X86_FP80Size :: FloatSize X86_80Float
deriving instance Eq (FloatSize fi)
deriving instance Ord (FloatSize fi)
deriving instance Show (FloatSize fi)
instance TestEquality FloatSize where
  testEquality SingleSize SingleSize = Just Refl
  testEquality DoubleSize DoubleSize = Just Refl
  testEquality X86_FP80Size X86_FP80Size = Just Refl
  testEquality _ _ = Nothing

-- | This datatype describes the variety of values that can be stored in
--   the LLVM heap.
data LLVMVal sym where
  -- NOTE! The ValInt constructor uniformly represents both pointers and
  -- raw bitvector values.  The 'SymNat' value is an allocation block number
  -- that identifies specific allocations.  The block number '0' is special,
  -- and indicates that this value is actually a bitvector.  Non-zero block
  -- numbers correspond to pointer values, where the 'SymBV' value is an
  -- offset from the base pointer of the allocation.
  LLVMValInt :: (1 <= w) => SymNat sym -> SymBV sym w -> LLVMVal sym
  LLVMValFloat :: FloatSize fi -> SymInterpretedFloat sym fi -> LLVMVal sym
  LLVMValStruct :: Vector (Field StorageType, LLVMVal sym) -> LLVMVal sym
  LLVMValArray :: StorageType -> Vector (LLVMVal sym) -> LLVMVal sym

  -- The zero value exists at all storable types, and represents the the value
  -- which is obtained by loading the approprite number of all zero bytes.
  -- It is useful for compactly representing large zero-initialized data structures.
  LLVMValZero :: StorageType -> LLVMVal sym


llvmValStorableType :: IsExprBuilder sym => LLVMVal sym -> StorageType
llvmValStorableType v =
  case v of
    LLVMValInt _ bv -> bitvectorType (bitsToBytes (natValue (bvWidth bv)))
    LLVMValFloat SingleSize _ -> floatType
    LLVMValFloat DoubleSize _ -> doubleType
    LLVMValFloat X86_FP80Size _ -> x86_fp80Type
    LLVMValStruct fs -> structType (fmap fst fs)
    LLVMValArray tp vs -> arrayType (fromIntegral (V.length vs)) tp
    LLVMValZero tp -> tp

-- | Coerce an 'LLVMPtr' value into a memory-storable 'LLVMVal'.
ptrToPtrVal :: (1 <= w) => LLVMPtr sym w -> LLVMVal sym
ptrToPtrVal (LLVMPointer blk off) = LLVMValInt blk off

----------------------------------------------------------------------
-- PartLLVMVal

newtype Pred' sym = Pred' (Pred sym)

instance TestEquality (SymExpr sym) => Eq (Pred' sym) where
  Pred' x == Pred' y = isJust (testEquality x y) 

instance OrdF (SymExpr sym) => Ord (Pred' sym) where
  compare (Pred' x) (Pred' y) = toOrdering (compareF x y)

pred' :: Simple Lens (Pred' sym) (Pred sym)
pred' f (Pred' x) = Pred' <$> f x

-- | Partial LLVM values.
data PartLLVMVal sym
  = PartLLVMVal (Map (Pred' sym) String) (LLVMVal sym)
  | NoLLVMVal String

partValPreds :: IsSymInterface sym => sym -> PartLLVMVal sym -> Map (Pred' sym) String
partValPreds _   (PartLLVMVal ps _) = ps
partValPreds sym (NoLLVMVal msg) = Map.singleton (Pred' (falsePred sym)) msg

zeroInt ::
  IsSymInterface sym =>
  sym ->
  Bytes ->
  (forall w. (1 <= w) => Maybe (SymNat sym, SymBV sym w) -> IO a) ->
  IO a
zeroInt sym bytes k
   | Just (Some w) <- someNat (bytesToBits bytes)
   , Just LeqProof <- isPosNat w
   =   do blk <- natLit sym 0
          bv  <- bvLit sym w 0
          k (Just (blk, bv))
zeroInt _ _ k = k @1 Nothing


bvToFloatPartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvToFloatPartLLVMVal sym (PartLLVMVal ps (LLVMValZero (StorageType (Bitvector 4) _))) =
  PartLLVMVal ps . LLVMValFloat SingleSize
    <$> (iFloatFromBinary sym SingleFloatRepr =<< bvLit sym (knownNat @32) 0)

bvToFloatPartLLVMVal sym (PartLLVMVal ps v@(LLVMValInt blk off))
  | Just Refl <- testEquality (bvWidth off) (knownNat @32)
  = do pz <- natEq sym blk =<< natLit sym 0
       let msg = "Invalid pointer to float cast:\n   " ++ show v
       PartLLVMVal (Map.insert (Pred' pz) msg ps) . LLVMValFloat SingleSize
         <$> iFloatFromBinary sym SingleFloatRepr off

bvToFloatPartLLVMVal _ (PartLLVMVal _ v) =
  let msg = "Unexpected value in bitvector to float cast:\n  " ++ show v
   in return $ NoLLVMVal msg

bvToFloatPartLLVMVal _ v@(NoLLVMVal _) = return v


bvToDoublePartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvToDoublePartLLVMVal sym (PartLLVMVal ps (LLVMValZero (StorageType (Bitvector 8) _))) =
  PartLLVMVal ps . LLVMValFloat DoubleSize
    <$> (iFloatFromBinary sym DoubleFloatRepr =<< bvLit sym (knownNat @64) 0)

bvToDoublePartLLVMVal sym (PartLLVMVal ps v@(LLVMValInt blk off))
  | Just Refl <- testEquality (bvWidth off) (knownNat @64)
  = do pz <- natEq sym blk =<< natLit sym 0
       let msg = "Invalid pointer to double cast:\n  " ++ show v
       PartLLVMVal (Map.insert (Pred' pz) msg ps) . LLVMValFloat DoubleSize
         <$> iFloatFromBinary sym DoubleFloatRepr off

bvToDoublePartLLVMVal _ (PartLLVMVal _ v) =
  let msg = "Unexpected value in bitvector to double cast:\n  " ++ show v
   in return $ NoLLVMVal msg

bvToDoublePartLLVMVal _ v@(NoLLVMVal _) = return v


bvToX86_FP80PartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvToX86_FP80PartLLVMVal sym (PartLLVMVal ps (LLVMValZero (StorageType (Bitvector 10) _))) =
  PartLLVMVal ps . LLVMValFloat X86_FP80Size
    <$> (iFloatFromBinary sym X86_80FloatRepr =<< bvLit sym (knownNat @80) 0)

bvToX86_FP80PartLLVMVal sym (PartLLVMVal ps v@(LLVMValInt blk off))
  | Just Refl <- testEquality (bvWidth off) (knownNat @80)
  = do pz <- natEq sym blk =<< natLit sym 0
       let msg = "Invalid pointer to X86_FP80 cast:\n  " ++ show v
       PartLLVMVal (Map.insert (Pred' pz) msg ps) . LLVMValFloat X86_FP80Size <$> iFloatFromBinary sym X86_80FloatRepr off

bvToX86_FP80PartLLVMVal _ (PartLLVMVal _ v) =
  let msg = "Unexpected value in bitvector fo X86_FP80 cast:\n  " ++ show v
   in return $ NoLLVMVal msg

bvToX86_FP80PartLLVMVal _ v@(NoLLVMVal _) = return v


-- | Concatenate partial LLVM bitvector values. The least-significant
-- (low) bytes are given first. The allocation block number of each
-- argument is asserted to equal 0, indicating non-pointers.
bvConcatPartLLVMVal :: forall sym.
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
bvConcatPartLLVMVal _ (NoLLVMVal msg) (NoLLVMVal _)     = return $ NoLLVMVal msg
bvConcatPartLLVMVal _ (PartLLVMVal _ _) (NoLLVMVal msg) = return $ NoLLVMVal msg
bvConcatPartLLVMVal _ (NoLLVMVal msg) (PartLLVMVal _ _) = return $ NoLLVMVal msg

bvConcatPartLLVMVal sym (PartLLVMVal ps1 v1) (PartLLVMVal ps2 v2) =
    case (v1, v2) of
      (LLVMValInt blk_low low, LLVMValInt blk_high high) ->
        do go blk_low low blk_high high
      (LLVMValInt blk_low low, LLVMValZero (StorageType (Bitvector high_bytes) _)) ->
        zeroInt sym high_bytes $ \case
          Nothing ->
            return (PartLLVMVal (ps1 <> ps2) v1)
          Just (blk_high, high) ->
            go blk_low low blk_high high
      (LLVMValZero (StorageType (Bitvector low_bytes) _), LLVMValInt blk_high high) ->
        zeroInt sym low_bytes $ \case
          Nothing ->
            return (PartLLVMVal (ps1 <> ps2) v2)
          Just (blk_low, low) ->
            go blk_low low blk_high high
      (LLVMValZero (StorageType (Bitvector low_bytes) _), LLVMValZero (StorageType (Bitvector high_bytes) _)) ->
        return (PartLLVMVal (ps1 <> ps2) (LLVMValZero (bitvectorType (low_bytes + high_bytes))))

      _ ->
        let msg = "Unexpected value in bitvector concatenation:\n  " ++ show v1 ++ "\n  " ++ show v2
         in return $ NoLLVMVal msg

 where
  go :: forall l h. (1 <= l, 1 <= h) =>
    SymNat sym -> SymBV sym l -> SymNat sym -> SymBV sym h -> IO (PartLLVMVal sym)
  go blk_low low blk_high high
    -- NB we check that the things we are concatenating are each an integral number of
    -- bytes.  This prevents us from concatenating together the partial-byte writes that
    -- result from e.g. writing an i1 or an i20 into memory.  This is consistent with LLVM
    -- documentation, which says that non-integral number of bytes loads will only succeed
    -- if the value was written orignally with the same type.
    | natValue low_w' `mod` 8 == 0
    , natValue high_w' `mod` 8 == 0 =
      do blk0   <- natLit sym 0
         p_blk1 <- natEq sym blk_low blk0
         p_blk2 <- natEq sym blk_high blk0
         Just LeqProof <- return $ isPosNat (addNat high_w' low_w')
         let msg1 = "Invalid concatenation of pointer value:\n  " ++ show v1
         let msg2 = "Invalid concatenation of pointer value:\n  " ++ show v2
         bv <- bvConcat sym high low
         let ps = Map.insert (Pred' p_blk1) msg1 $ Map.insert (Pred' p_blk2) msg2 $ ps1 <> ps2
         return $ PartLLVMVal ps $ LLVMValInt blk0 bv

    | otherwise =
        let msg = "Cannot concatenate bitvectors that are non-integral numbers of bytes:" ++
                  "\n  low width: " ++ show low_w' ++
                  "\n  high width: " ++ show  high_w'  
         in return $ NoLLVMVal msg

    where low_w' = bvWidth low
          high_w' = bvWidth high

-- | Cons an element onto a partial LLVM array value.
consArrayPartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
consArrayPartLLVMVal _sym (PartLLVMVal p1 (LLVMValZero tp)) (PartLLVMVal p2 (LLVMValZero (StorageType (Array m tp') _)))
  | tp == tp' =
       return $ PartLLVMVal (p1 <> p2) $ LLVMValZero (arrayType (m+1) tp')

consArrayPartLLVMVal _sym (PartLLVMVal p1 hd) (PartLLVMVal p2 (LLVMValZero (StorageType (Array m tp) _)))
  | llvmValStorableType hd == tp =
       return $ PartLLVMVal (p1 <> p2) $ LLVMValArray tp (V.cons hd (V.replicate (fromIntegral m) (LLVMValZero tp)))

consArrayPartLLVMVal _sym (PartLLVMVal p1 hd) (PartLLVMVal p2 (LLVMValArray tp vec))
  | llvmValStorableType hd == tp =
       return $ PartLLVMVal (p1 <> p2) $ LLVMValArray tp (V.cons hd vec)

consArrayPartLLVMVal _ (PartLLVMVal _ v1) (PartLLVMVal _ v2) =
  let msg = "Unexpected values in cons array:" ++
            "\n  : " ++ show v1 ++
            "\n  : " ++ show v2
   in return $ NoLLVMVal msg

consArrayPartLLVMVal _sym (NoLLVMVal msg) _ =
   return $ NoLLVMVal msg
consArrayPartLLVMVal _sym _ (NoLLVMVal msg) =
   return $ NoLLVMVal msg

-- | Append two partial LLVM array values.
appendArrayPartLLVMVal ::
  IsSymInterface sym =>
  sym ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
appendArrayPartLLVMVal _sym
  (PartLLVMVal p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (PartLLVMVal p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 =
        return $ PartLLVMVal (p1 <> p2) $ LLVMValZero (arrayType (n1+n2) tp1)

appendArrayPartLLVMVal _sym
  (PartLLVMVal p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (PartLLVMVal p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
     do let v1 = V.replicate (fromIntegral n1) (LLVMValZero tp1)
        return $ PartLLVMVal (p1<>p2) $ LLVMValArray tp1 (v1 V.++ v2)

appendArrayPartLLVMVal _sym
  (PartLLVMVal p1 (LLVMValArray tp1 v1))
  (PartLLVMVal p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 =
     do let v2 = V.replicate (fromIntegral n2) (LLVMValZero tp1)
        return $ PartLLVMVal (p1 <> p2) $ LLVMValArray tp1 (v1 V.++ v2)

appendArrayPartLLVMVal _sym
  (PartLLVMVal p1 (LLVMValArray tp1 v1))
  (PartLLVMVal p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
         return $ PartLLVMVal (p1 <> p2) $ LLVMValArray tp1 (v1 V.++ v2)

appendArrayPartLLVMVal _ (PartLLVMVal _ v1) (PartLLVMVal _ v2) =
  let msg = "Unexpected values when appending arrays:" ++
            "\n  :" ++ show v1 ++
            "\n  :" ++ show v2
   in return $ NoLLVMVal msg
appendArrayPartLLVMVal _ (NoLLVMVal msg) _ =
   return $ NoLLVMVal msg
appendArrayPartLLVMVal _ _ (NoLLVMVal msg) =
   return $ NoLLVMVal msg

-- | Make a partial LLVM array value.
mkArrayPartLLVMVal :: forall sym .
  IsSymInterface sym => sym ->
  StorageType ->
  Vector (PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
mkArrayPartLLVMVal _sym tp vec =
  do let f :: PartLLVMVal sym -> ExceptT String (State (Map (Pred' sym) String)) (LLVMVal sym)
         f (NoLLVMVal msg) = throwE msg
         f (PartLLVMVal p1 x) =
           do p0 <- get
              put (p0 <> p1)
              return x
     let x = flip runState mempty $ runExceptT (traverse f vec)
     case x of
       (Left msg, _)    -> return $ NoLLVMVal msg
       (Right vec', ps) -> return $ PartLLVMVal ps $ LLVMValArray tp vec'

-- | Make a partial LLVM struct value.
mkStructPartLLVMVal :: forall sym .
  IsSymInterface sym => sym ->
  Vector (Field StorageType, PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
mkStructPartLLVMVal _sym vec =
  do let f :: (Field StorageType, PartLLVMVal sym)
           -> ExceptT String (State (Map (Pred' sym) String)) (Field StorageType, LLVMVal sym)
         f (_fld, NoLLVMVal msg) = throwE msg
         f (fld, PartLLVMVal p1 x) =
             do p0 <- get
                put (p0 <> p1)
                return (fld, x)
     let x = flip runState mempty $ runExceptT (traverse f vec)
     case x of
       (Left msg, _)   -> return $ NoLLVMVal msg
       (Right vec',ps) -> return $ PartLLVMVal ps $ LLVMValStruct vec'

-- | Select some of the least significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectLowBvPartLLVMVal ::
  IsSymInterface sym => sym ->
  Bytes ->
  Bytes ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

selectLowBvPartLLVMVal _sym low hi (PartLLVMVal ps (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ PartLLVMVal ps $ LLVMValZero (bitvectorType low)

selectLowBvPartLLVMVal sym low hi (PartLLVMVal ps v@(LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (bytesToBits low)
  , Just (Some (hi_w))  <- someNat (bytesToBits hi)
  , Just LeqProof <- isPosNat low_w
  , Just Refl <- testEquality (addNat low_w hi_w) w
  , Just LeqProof <- testLeq low_w w =
    do pz <- natEq sym blk =<< natLit sym 0
       let msg = "Cannot select low bytes from pointer values:\n  " ++ show v
       bv' <- bvSelect sym (knownNat :: NatRepr 0) low_w bv
       return $ PartLLVMVal (Map.insert (Pred' pz) msg ps) (LLVMValInt blk bv')
  where w = bvWidth bv

selectLowBvPartLLVMVal _ _ _ (PartLLVMVal _ v) =
  let msg = "Unexpected value in bitvector select:\n  " ++ show v
   in return $ NoLLVMVal msg

selectLowBvPartLLVMVal _ _ _ v@(NoLLVMVal _) = return v


-- | Select some of the most significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectHighBvPartLLVMVal ::
  IsSymInterface sym => sym ->
  Bytes ->
  Bytes ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

selectHighBvPartLLVMVal _sym low hi (PartLLVMVal ps (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ PartLLVMVal ps $ LLVMValZero (bitvectorType hi)

selectHighBvPartLLVMVal sym low hi (PartLLVMVal ps v@(LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (bytesToBits low)
  , Just (Some (hi_w))  <- someNat (bytesToBits hi)
  , Just LeqProof <- isPosNat hi_w
  , Just Refl <- testEquality (addNat low_w hi_w) w =
    do pz' <- natEq sym blk =<< natLit sym 0
       bv' <- bvSelect sym low_w hi_w bv
       let msg = "Cannot select high bytes from pointer values:\n  " ++ show v
       return $ PartLLVMVal (Map.insert (Pred' pz') msg ps) $ LLVMValInt blk bv'
  where w = bvWidth bv

selectHighBvPartLLVMVal _ _ _ (PartLLVMVal _ v) =
  let msg = "Unexpected value in bitvector select:\n  " ++ show v
   in return $ NoLLVMVal msg

selectHighBvPartLLVMVal _ _ _ v@(NoLLVMVal _) = return v


-- | Look up an element in a partial LLVM array value.
arrayEltPartLLVMVal ::
  IsSymInterface sym =>
  sym ->
  Word64 -> StorageType -> Word64 ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
arrayEltPartLLVMVal _sym sz tp idx (PartLLVMVal p (LLVMValArray tp' vec))
  | sz == fromIntegral (V.length vec)
  , 0 <= idx
  , idx < sz
  , tp == tp' =
    return $ PartLLVMVal p (vec V.! fromIntegral idx)

arrayEltPartLLVMVal _ _ _ _ (PartLLVMVal _ v) =
  let msg = "Unexpected value in LLVM array select:\n  " ++ show v
   in return $ NoLLVMVal msg

arrayEltPartLLVMVal _ _ _ _ v@(NoLLVMVal _) = return v


-- | Look up a field in a partial LLVM struct value.
fieldValPartLLVMVal ::
  IsSymInterface sym =>
  sym ->
  (Vector (Field StorageType)) -> Int ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
fieldValPartLLVMVal _ flds idx (PartLLVMVal ps (LLVMValStruct vec))
  | flds == fmap fst vec
  , 0 <= idx
  , idx < V.length vec =
    return $ PartLLVMVal ps $ snd $ (vec V.! idx)

fieldValPartLLVMVal _ _ _ (PartLLVMVal _ v) =
  let msg = "Unexpected value in LLVM struct select:\n  " ++ show v
   in return $ NoLLVMVal msg

fieldValPartLLVMVal _ _ _ v@(NoLLVMVal _) = return v


-- | Mux partial LLVM values.
muxLLVMVal :: forall sym
    . IsSymInterface sym
   => sym
   -> Pred sym
   -> PartLLVMVal sym
   -> PartLLVMVal sym
   -> IO (PartLLVMVal sym)
muxLLVMVal sym = mux
  where
    mux _cond (NoLLVMVal msg) (NoLLVMVal _) =
      return $ NoLLVMVal msg

    mux cond (NoLLVMVal msg) (PartLLVMVal ps2 v) =
      PartLLVMVal <$> muxpreds cond (Map.singleton (Pred' (falsePred sym)) msg) ps2 <*> return v

    mux cond (PartLLVMVal ps1 v) (NoLLVMVal msg) =
      PartLLVMVal <$> muxpreds cond ps1 (Map.singleton (Pred' (falsePred sym)) msg) <*> return v

    mux cond (PartLLVMVal ps1 v1) (PartLLVMVal ps2 v2) =
      do ps <- muxpreds cond ps1 ps2
         muxval cond v1 v2 >>= \case
           NoLLVMVal msg -> return $ NoLLVMVal msg
           PartLLVMVal ps' v -> return $ PartLLVMVal (ps <> ps') v

    muxpreds :: Pred sym -> Map (Pred' sym) String -> Map (Pred' sym) String -> IO (Map (Pred' sym) String)
    muxpreds cond xs ys =
      do notcond <- notPred sym cond
         xs' <- (traverse . _1 . pred') (impliesPred sym cond) (Map.toList xs)
         ys' <- (traverse . _1 . pred') (impliesPred sym notcond) (Map.toList ys)
         return (Map.fromList (xs' ++ ys'))

    muxval :: Pred sym -> LLVMVal sym -> LLVMVal sym -> IO (PartLLVMVal sym)

    muxval cond (LLVMValZero tp) v =
      do PartLLVMVal mempty <$> muxzero cond tp v

    muxval cond v (LLVMValZero tp) =
      do cond' <- notPred sym cond
         PartLLVMVal mempty <$> muxzero cond' tp v

    muxval cond (LLVMValInt base1 off1) (LLVMValInt base2 off2)
      | Just Refl <- testEquality (bvWidth off1) (bvWidth off2)
      = do base <- natIte sym cond base1 base2
           off  <- bvIte sym cond off1 off2
           return $ PartLLVMVal mempty $ LLVMValInt base off

    muxval cond (LLVMValFloat (xsz :: FloatSize fi) x) (LLVMValFloat ysz y)
      | Just Refl <- testEquality xsz ysz
      = PartLLVMVal mempty . LLVMValFloat xsz <$> (iFloatIte @_ @fi sym cond x y)

    muxval cond (LLVMValStruct fls1) (LLVMValStruct fls2)
      | fmap fst fls1 == fmap fst fls2 = do
          fls <- traverse id $ V.zipWith (\(f,x) (_,y) -> (f,) <$> muxval cond x y) fls1 fls2
          mkStructPartLLVMVal sym fls

    muxval cond (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
      | tp1 == tp2 && V.length v1 == V.length v2 = do
          v <- traverse id $ V.zipWith (muxval cond) v1 v2
          mkArrayPartLLVMVal sym tp1 v

    muxval _cond v1 v2 =
      let msg = "LLVM Value mismatch at merge point:" ++
                "\n  " ++ show v1 ++
                "\n  " ++ show v2
       in return $ NoLLVMVal msg

    muxzero :: Pred sym -> StorageType -> LLVMVal sym -> IO (LLVMVal sym)
    muxzero cond _tp val = case val of
      LLVMValZero tp -> return $ LLVMValZero tp
      LLVMValInt base off ->
        do zbase <- natLit sym 0
           zoff  <- bvLit sym (bvWidth off) 0
           base' <- natIte sym cond zbase base
           off'  <- bvIte sym cond zoff off
           return $ LLVMValInt base' off'
      LLVMValFloat SingleSize x ->
        do zerof <- iFloatLit sym SingleFloatRepr 0
           x'    <- iFloatIte @_ @SingleFloat sym cond zerof x
           return $ LLVMValFloat SingleSize x'
      LLVMValFloat DoubleSize x ->
        do zerof <- iFloatLit sym DoubleFloatRepr 0
           x'    <- iFloatIte @_ @DoubleFloat sym cond zerof x
           return $ LLVMValFloat DoubleSize x'
      LLVMValFloat X86_FP80Size x ->
        do zerof <- iFloatLit sym X86_80FloatRepr 0
           x'    <- iFloatIte @_ @X86_80Float sym cond zerof x
           return $ LLVMValFloat X86_FP80Size x'

      LLVMValArray tp vec ->
        LLVMValArray tp <$> traverse (muxzero cond tp) vec

      LLVMValStruct flds ->
        LLVMValStruct <$> traverse (\(fld, v) -> (fld,) <$> muxzero cond (fld^.fieldVal) v) flds




instance IsExpr (SymExpr sym) => Show (LLVMVal sym) where
  show (LLVMValZero _tp) = "0"
  show (LLVMValInt blk w)
    | Just 0 <- asNat blk = "<int" ++ show (bvWidth w) ++ ">"
    | otherwise = "<ptr " ++ show (bvWidth w) ++ ">"
  show (LLVMValFloat SingleSize _) = "<float>"
  show (LLVMValFloat DoubleSize _) = "<double>"
  show (LLVMValFloat X86_FP80Size _) = "<long double>"
  show (LLVMValStruct xs) =
    unwords $ [ "{" ]
           ++ intersperse ", " (map (show . snd) $ V.toList xs)
           ++ [ "}" ]
  show (LLVMValArray _ xs) =
    unwords $ [ "[" ]
           ++ intersperse ", " (map show $ V.toList xs)
           ++ [ "]" ]
