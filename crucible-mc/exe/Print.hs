{-# Language OverloadedStrings, TypeFamilies #-}
module Print where

import Text.PrettyPrint

import Data.Parameterized.Some

import Lang.Crucible.Simulator.ExecutionTree


ppExecState :: ExecState p sym ext rtp -> Doc
ppExecState st =
  case st of
    ResultState {} -> "ResultState"
    AbortState {}  -> "AbortState"
    UnwindCallState {} -> "UnwindCallState"
    CallState {} -> "CallState"
    TailCallState {} -> "TailCallState"
    ReturnState {} -> "ReturnState"
    RunningState ri _st -> "RunningState" <+> ppRunningStateInfo ri
    SymbolicBranchState {} -> "SymbolicBranchState"

    ControlTransferState res _st ->
      "ControlTransferState" <+> ppControlResumption res

    OverrideState {} -> "OverrideState"
    BranchMergeState t _st -> "BranchMergeState" <+> text (ppBranchTarget t)
    InitialState {} -> "InitialState"

ppControlResumption :: ControlResumption p sym ext rtp f -> Doc
ppControlResumption res =
  case res of
    ContinueResumption jmp -> "Continue" <+> ppResolvedJump jmp
    CheckMergeResumption jmp -> "CheckMerge" <+> ppResolvedJump jmp
    SwitchResumption _opts -> "Switch"
    OverrideResumption _code _regs -> "Override"

ppResolvedJump :: ResolvedJump sym blocks -> Doc
ppResolvedJump jmp =
  case jmp of
    ResolvedJump bid _regs -> ppShow bid

ppRunningStateInfo :: RunningStateInfo blocks args -> Doc
ppRunningStateInfo rs =
  case rs of
    RunBlockStart bid      -> "BlockStart"      <+> ppShow bid
    RunBlockEnd (Some bid) -> "BlockEnd"        <+> ppShow bid
    RunReturnFrom f        -> "ReturnFrom"      <+> ppShow f
    RunPostBranchMerge bid -> "PostBranchMerge" <+> ppShow bid


ppShow :: Show a => a -> Doc
ppShow = text . show



