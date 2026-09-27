import VV
import Lean.Util.CollectAxioms
import Lean.DeclarationRange

/-! All imported project declarations are audited, including private ones.
Only the listed proof bodies may be abstracted. Their types are checked first
without any admission abstraction. No user axiom or opaque interface is allowed.
Unsafe, sourceless compiler implementation copies are excluded only as roots.
A passed audit is not a proof of any admitted statement. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let admissions : Array Name := #[`VV.P5FiniteCheck.rank_check_10_14, `VV.BBEKCompactEntropyCore.no_positive_entropy_supported_K]
  do
    let info ← getConstInfo `VV.P5FiniteCheck.rank_check_10_14
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Admitted proof is not a theorem: VV.P5FiniteCheck.rank_check_10_14"
    Lean.Elab.Command.liftTermElabM do
      let expected ← Lean.Elab.Term.elabTerm (← `(((VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true))) none
      unless ← Lean.Meta.isDefEq info.type expected do
        throwError "Unexpected admitted signature: VV.P5FiniteCheck.rank_check_10_14"
      let expected ← Lean.instantiateMVars expected
      if expected.hasMVar then throwError "Unresolved metavariable in admitted signature"
  do
    let info ← getConstInfo `VV.BBEKCompactEntropyCore.no_positive_entropy_supported_K
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Admitted proof is not a theorem: VV.BBEKCompactEntropyCore.no_positive_entropy_supported_K"
    Lean.Elab.Command.liftTermElabM do
      let expected ← Lean.Elab.Term.elabTerm (← `((∀ (μ : MeasureTheory.Measure VV.BBEKQuotient.X)
    [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.SMulInvariantMeasure VV.BBEKDiagonal.A VV.BBEKQuotient.X μ]
    [ErgodicSMul VV.BBEKDiagonal.A VV.BBEKQuotient.X μ]
    {δ : ℝ}, 0 < δ → μ (VV.BBEKOrbit.K δ) = 1 →
    ∀ (hμT : MeasureTheory.MeasurePreserving
      (VV.BBEKEntropyExpansion.timeMap VV.BBEKDynamics.time0) μ μ),
      0 < ErgodicTheory.Entropy.ksEntropy hμT → False))) none
      unless ← Lean.Meta.isDefEq info.type expected do
        throwError "Unexpected admitted signature: VV.BBEKCompactEntropyCore.no_positive_entropy_supported_K"
      let expected ← Lean.instantiateMVars expected
      if expected.hasMVar then throwError "Unresolved metavariable in admitted signature"

  let mut typeState : CollectAxioms.State := {}
  for name in admissions do
    let info ← getConstInfo name
    for dependency in info.type.getUsedConstants do
      let (_,next) := ((CollectAxioms.collect dependency).run env).run typeState
      typeState := next
    for a in typeState.axioms do
      unless allowed.contains a do
        throwError "Forbidden axiom in admitted signature {name}: {a}"
    logInfo m!"ADMITTED SIGNATURE CHECKED WITHOUT ABSTRACTION: {name}: {info.type}"
    let raw ← collectAxioms name
    for a in raw do
      unless allowed.contains a || a == `sorryAx do
        throwError "Forbidden axiom in admitted proof {name}: {a}"
    logInfo m!"RAW ADMISSION AXIOMS {name}: {raw}"
  let mut state := typeState
  for name in admissions do
    state := { state with visited := state.visited.insert name }
  let mut theorems := 0
  let mut definitions := 0
  let mut compilerCopies := 0
  for (name,info) in env.constants.toList do
    let fromProject := match env.getModuleIdxFor? name with
      | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        (`VV).isPrefixOf m || (`Foundations).isPrefixOf m || (`Research).isPrefixOf m
      | none => false
    if (`VV).isPrefixOf name || fromProject then
      let compilerName : Bool := match name with
        | .str _ s => s.startsWith "_cstage" || s.startsWith "_spec_" || s.startsWith "_elambda"
        | _ => false
      let compilerKind : Bool := match info with
        | .defnInfo _ | .axiomInfo _ => true
        | _ => false
      let codegenCopy := compilerName && compilerKind && info.isUnsafe &&
        (← findDeclarationRangesCore? name).isNone
      match info with
      | .axiomInfo _ => unless codegenCopy do
          throwError "Forbidden project axiom: {name}"
      | .opaqueInfo _ => throwError "Forbidden project opaque: {name}"
      | _ => pure ()
      if codegenCopy then
        compilerCopies := compilerCopies + 1
      else
        let (_,next) := ((CollectAxioms.collect name).run env).run state
        state := next
        for a in state.axioms do
          unless allowed.contains a do
            throwError "Forbidden dependency of {name}: {a}"
        match info with
        | .thmInfo _ => theorems := theorems + 1
        | .defnInfo _ => definitions := definitions + 1
        | _ => pure ()
  if theorems = 0 then throwError "No project theorem audited."
  logInfo m!"THEORY AXIOMS AFTER EXACT PROOF ABSTRACTIONS: {state.axioms}"
  logInfo m!"PASS: {theorems} theorem declarations and {definitions} definitions audited."
  logInfo m!"ADMISSION COUNT: {admissions.size}; unsafe compiler roots excluded: {compilerCopies}"
#check VV.problem3_classification
#check VV.Problem4.problem4_all_periods
#check VV.Problem4.card_class_three
#check VV.Problem4.card_class_four
#check VV.P5SmallCertificate.frequently_three_within_two
#check VV.bbekTheorem42
#check VV.problem7
#print axioms VV.P5FiniteCheck.rank_check_10_14
#print axioms VV.P5FiniteCheck.problem5_bound_eleven
#print axioms VV.BBEKCompactEntropyCore.no_positive_entropy_supported_K
#print axioms VV.bbekTheorem42
#print axioms VV.problem7

