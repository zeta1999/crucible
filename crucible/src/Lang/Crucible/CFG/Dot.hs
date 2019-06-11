-- | This module renders a CFG into "dot", the graph format used by "graphviz".
module Lang.Crucible.CFG.Dot(cfgToDot, cfgSaveDot) where

import Data.Char(isDigit)
import Data.Parameterized.TraversableFC(foldrFC)
import Lang.Crucible.CFG.Core

-- | Render a CFG in the "dot" format, and save it to the given file.
cfgSaveDot :: FilePath -> CFG ext blocks init ret -> IO ()
cfgSaveDot file cfg = writeFile file (cfgToDot cfg)

-- | Render a CFG to the "dot" format.
cfgToDot :: CFG ext blocks init ret -> String
cfgToDot cfg = unlines $
  [ "digraph G {"
  , "size=\"6,4\";"
  , "ratio=\"fill\";"
  ] ++ foldrFC (\s xs -> seeNode s ++ xs) [] (cfgBlockMap cfg) ++
  [ "}" ]

seeNode :: Block ext blocks ret ctx -> [String]
seeNode b = withBlockTermStmt b $ \_ ts -> [ me ++ n ++ ";" | n <- seeNext ts ]
  where me = "  " ++ seeBlockId (blockID b) ++ " -> "

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

seeJumpTarget :: JumpTarget blocks ctx -> String
seeJumpTarget (JumpTarget bid _ _) = seeBlockId bid

seeSwitchTarget :: SwitchTarget blocks ctx tp -> String
seeSwitchTarget (SwitchTarget bid _ _) = seeBlockId bid

seeBlockId :: BlockID blocks tp -> String
seeBlockId = filter isDigit . show


