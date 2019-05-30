{-# Language ExistentialQuantification, GADTs, BlockArguments #-}
module Loop where

import Data.Char(isDigit)
import Data.Parameterized.TraversableFC(foldrFC)
import Lang.Crucible.CFG.Core
import Lang.Crucible.Analysis.Fixpoint.Components

see :: CFG ext blocks init ret -> String
see cfg = unlines $ map show $ cfgWeakTopologicalOrdering cfg

saveGraph :: FilePath -> CFG ext blocks init ret -> IO ()
saveGraph file cfg = writeFile file (seeGraph cfg)

seeGraph :: CFG ext blocks init ret -> String
seeGraph cfg = unlines $
  [ "digraph G {"
  , "size=\"6,4\";"
  , "ratio=\"fill\";"
  ] ++ foldrFC (\s xs -> seeNode s ++ xs) [] (cfgBlockMap cfg) ++
  [ "}" ]

seeNode :: Block ext blocks ret ctx -> [String]
seeNode b = withBlockTermStmt b \_ ts ->
  let me = seeBlockId (blockID b) ++ " -> "
  in [ me ++ n ++ ";" | n <- seeNext ts ]

seeNext :: TermStmt blocks ret ctx -> [String]
seeNext ts =
  case ts of
    Jump jt -> [seeJumpTarget jt]
    Br _ jt1 jt2 -> [ seeJumpTarget jt1, seeJumpTarget jt2 ]
    MaybeBranch _ _ st jt -> [ seeSwitchTarget st, seeJumpTarget jt ]
    VariantElim _ _ sts -> foldrFC (\s xs -> seeSwitchTarget s : xs) [] sts
    Return {} -> []
    TailCall {} -> []
    ErrorStmt {} -> []

seeBlockId :: BlockID blocks tp -> String
seeBlockId = filter isDigit . show

seeJumpTarget :: JumpTarget blocks ctx -> String
seeJumpTarget (JumpTarget bid _ _) = seeBlockId bid

seeSwitchTarget :: SwitchTarget blocks ctx tp -> String
seeSwitchTarget (SwitchTarget bid _ _) = seeBlockId bid





