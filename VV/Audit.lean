import VV
import VV.BBEKFinal
import Lean.Util.CollectAxioms
import Lean.DeclarationRange

/-!
Audit every imported project declaration, including private declarations.
Exactly two named theorem proofs may be abstracted:

* `VV.P5FiniteCheck.rank_check_10_14`: the unexecuted finite Boolean check;
* `VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy`: the explicitly
  unfinished theoretical EL low-entropy input.

Both signatures are checked against fixed expressions. Their type dependencies
are recursively audited WITHOUT either abstraction, so a `sorry` in a type,
instance, or definition used by either signature is rejected. Only after this
check are the two proof declarations excluded from the recursive theory audit.
All remaining mathematical dependencies must use only `propext`,
`Classical.choice`, and `Quot.sound`. Every project source `axiom` or `opaque`
is rejected, even if it is unused. This audit proves neither admitted statement.

Lean compiler-stage implementation declarations (`_cstage`, `_spec_`, `_elambda`)
are not mathematical definitions: code generation erases proofs using
`lcProof`. The old compiler also exports unsafe `axiomInfo` implementation
placeholders. Only unsafe definitions or axiom placeholders with these compiler
names AND no source declaration range are skipped as audit roots; source
axioms and every opaque declaration are rejected. `Check-VV.ps1` separately
rejects source-level axiom/opaque commands. All mathematical dependencies,
including dependencies on any implementation copy, are still audited;
neither these placeholders nor `lcProof` are allowed mathematical axioms.
-/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let finiteCheck := `VV.P5FiniteCheck.rank_check_10_14
  let lowEntropyCore := `VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy
  let admissions := #[finiteCheck, lowEntropyCore]
  let finiteInfo ← getConstInfo finiteCheck
  let coreInfo ← getConstInfo lowEntropyCore
  for name in admissions do
    match ← getConstInfo name with
    | .thmInfo _ => pure ()
    | _ => throwError "Allowed proof declaration is not a theorem: {name}"
  Lean.Elab.Command.liftTermElabM do
    let finiteExpected ← Lean.Elab.Term.elabTerm
      (← `((VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true)) none
    unless ← Lean.Meta.isDefEq finiteInfo.type finiteExpected do
      throwError "Admitted finite check has an unexpected type."
    let coreExpected ← Lean.Elab.Term.elabTerm
      (← `(∀ (μ : MeasureTheory.Measure VV.BBEKQuotient.X)
          [MeasureTheory.IsProbabilityMeasure μ]
          [MeasureTheory.SMulInvariantMeasure VV.BBEKDiagonal.A VV.BBEKQuotient.X μ]
          [ErgodicSMul VV.BBEKDiagonal.A VV.BBEKQuotient.X μ]
          (hμT : MeasureTheory.MeasurePreserving
            (VV.BBEKEntropyExpansion.timeMap VV.BBEKDynamics.time0) μ μ),
          0 < ErgodicTheory.Entropy.ksEntropy hμT →
          VV.BBEKPositiveExclusion.NoProperReductiveClosedOrbit μ →
          VV.BBEKLowEntropyCore.RootAlternative μ)) none
    unless ← Lean.Meta.isDefEq coreInfo.type coreExpected do
      throwError "Admitted low-entropy core has an unexpected type."
    for expected in #[finiteExpected, coreExpected] do
      let expected ← Lean.instantiateMVars expected
      if expected.hasMVar then
        throwError "An audited expected signature contains an unresolved metavariable."
  -- No admission is in this visited set. In particular, a reference from a
  -- signature to either admitted proof is followed and its sorry is rejected.
  let mut typeState : CollectAxioms.State := {}
  for name in admissions do
    let info ← getConstInfo name
    for dependency in info.type.getUsedConstants do
      let (_, nextState) := ((CollectAxioms.collect dependency).run env).run typeState
      typeState := nextState
    for a in typeState.axioms do
      unless allowed.contains a do
        throwError "Forbidden dependency in the TYPE of {name}: {a}"
    logInfo m!"ADMITTED SIGNATURE VERIFIED WITHOUT ABSTRACTION: {name}: {info.type}"
    let proofAxioms ← collectAxioms name
    for a in proofAxioms do
      unless allowed.contains a || a == `sorryAx do
        throwError "Forbidden dependency in admitted proof {name}: {a}"
    logInfo m!"RAW ADMITTED PROOF AXIOMS {name}: {proofAxioms}"
  logInfo m!"FINITE CHECK NOT EXECUTED: {finiteCheck}: {finiteInfo.type}"
  logInfo m!"EL LOW-ENTROPY THEORY NOT FORMALIZED: {lowEntropyCore}"
  logInfo m!"ADMITTED TYPE DEPENDENCIES: {typeState.axioms}"
  -- Share the visited set across declarations. This traverses every
  -- dependency once; only the two exact proof bodies are now abstracted.
  let mut auditState := { typeState with visited :=
    (typeState.visited.insert finiteCheck).insert lowEntropyCore }
  let mut theorems := 0
  let mut definitions := 0
  let mut otherDeclarations := 0
  let mut compilerCopies := 0
  for (name, info) in env.constants.toList do
    let fromProjectModule := match env.getModuleIdxFor? name with
      | some idx => (`VV).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if (`VV).isPrefixOf name || fromProjectModule then
      let compilerName : Bool := match name with
        | .str _ s =>
          (s.startsWith "_cstage" || s.startsWith "_spec_" || s.startsWith "_elambda")
        | _ => false
      let compilerKind : Bool := match info with
        | .defnInfo _ | .axiomInfo _ => true
        | _ => false
      let codegenCopy : Bool := compilerName && compilerKind && info.isUnsafe &&
        (← findDeclarationRangesCore? name).isNone
      match info with
      | .axiomInfo _ => unless codegenCopy do
          throwError "Forbidden project axiom: {name}"
      | .opaqueInfo _ => throwError "Forbidden project opaque declaration: {name}"
      | _ => pure ()
      if codegenCopy then
        compilerCopies := compilerCopies + 1
      else
        let (_, nextState) := ((CollectAxioms.collect name).run env).run auditState
        auditState := nextState
        for a in auditState.axioms do
          unless allowed.contains a do
            throwError "Forbidden dependency of {name}: {a}"
        match info with
        | .thmInfo _ =>
          if admissions.contains name then
            logInfo m!"ADMITTED PROOF ABSTRACTED, TYPE CHECKED: {name}"
          else
            logInfo m!"THEOREM {name}: checked (only the two named proofs abstracted)"
          theorems := theorems + 1
        | .defnInfo _ => definitions := definitions + 1
        | _ => otherDeclarations := otherDeclarations + 1
  if theorems = 0 then throwError "No project theorem was audited."
  logInfo m!"THEORY AXIOMS AFTER THE TWO EXACT PROOF ABSTRACTIONS: {auditState.axioms}"
  logInfo m!"PASS: {theorems} theorem declarations and {definitions} definitions audited."
  logInfo m!"ADDITIONAL COVERAGE: {otherDeclarations} inductive/constructor/recursor declarations audited; \
    {compilerCopies} unsafe compiler implementation copies excluded as roots."

-- Closed original Problem 3 classification.
#check VV.problem3_classification
#check VV.problem3_fixed_representative
#check VV.serret

-- Genuine class roots and the closed finite-template theorem.
#check VV.Problem4.finite_class_of_rooted_encoding
#check VV.Problem4.actual_class_count_le
#check VV.Problem4.rootedClassWord_injective
#check VV.Problem4.hasRootedEncoding
#check VV.Problem4.problem4_finiteness_and_bound
#check VV.Problem4.problem4_all_periods
-- Theory closed; one finite Boolean computation explicitly admitted.
#check VV.P5FiniteCheck.rank_check_10_14
#check VV.P5Window.problem5_of_finite_window_check
#check VV.P5FiniteCheck.problem5_bound_eleven
#check VV.P5FiniteCheck.eventual_every_31
-- The remaining low-entropy input is the second and sole theoretical admission.
#check VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy
#check VV.bbekTheorem42
#check VV.problem7
#check VV.P7RigidityReduction.RigidityCoverInput
#check VV.P7RigidityReduction.problem7_of_rigidity_cover
#check VV.P7BoxCover.BBEKTheorem42
#check VV.P7BoxCover.problem7_of_BBEK
-- BBEK Section 5: actual definitions and separately proved ingredients.
#check VV.BBEKDyadic.dyadic_integral_iff
#check VV.BBEKDynamics.cone_difference_all
#check VV.BBEKDynamics.time0_cone_unstable
#check VV.BBEKFiniteQuotients.prod_sl2_finiteIndex_eq_top
#check VV.BBEKOrbit.proposition51
#check VV.BBEKOrbit.isClosed_K
#check VV.BBEKNoncompact.K_ssubset_univ
#check VV.BBEKDiscrete.gamma_inter_ball_one
#check VV.BBEKDiscrete.gamma_discreteTopology
#check VV.BBEKDiscrete.gamma_isClosed
#check VV.BBEKDiscrete.quotient_t2Space
#check VV.BBEKDiscrete.quotient_locallyCompactSpace
#check VV.BBEKLocalChart.exists_open_injOn_mk
#check VV.BBEKLocalChart.chartHomeomorph
#check VV.BBEKLocalChart.isLocalHomeomorph_mk
#check VV.BBEKReduction.trappedParameters_compact
#check VV.BBEKReduction.BBEK_of_trapped_zero_box
#check VV.BBEKReduction.problem7_of_trapped_zero_box
#print axioms VV.P5FiniteCheck.problem5_bound_eleven
#print axioms VV.P5FiniteCheck.rank_check_10_14
#print axioms VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy
#print axioms VV.bbekTheorem42
#print axioms VV.problem7
#print axioms VV.BBEKFinal.full_root_of_rootAlternative
#print axioms VV.BBEKRootEscape.no_supported_of_any_nonzero_root
#print axioms VV.Problem4.problem4_finiteness_and_bound
#print axioms VV.Problem4.problem4_all_periods
#print axioms VV.P7RigidityReduction.problem7_of_rigidity_cover
#print axioms VV.P7BoxCover.problem7_of_BBEK
#print axioms VV.BBEKOrbit.proposition51
#print axioms VV.BBEKNoncompact.K_ssubset_univ
#print axioms VV.BBEKFiniteQuotients.prod_sl2_finiteIndex_eq_top
#print axioms VV.BBEKReduction.problem7_of_trapped_zero_box
#print axioms VV.BBEKDiscrete.gamma_inter_ball_one
#print axioms VV.BBEKLocalChart.isLocalHomeomorph_mk
#check VV.BBEKMahler.compact_K
#check VV.BBEKMahler.joint_orbit_closure_compact
#check VV.BBEKMautnerLp.quotient_psi_ergodic
#check VV.BBEKEntropyTrapped.trappedEntropy_pos_of_not_zero_box
#check VV.BBEKDiagonal.diagonal_decomposition
#check VV.BBEKDiagonalAverage.averaged_diagonal_ergodic
#check VV.BBEKCompactPreservation.compact_preimage_K
#print axioms VV.BBEKMahler.compact_K
#print axioms VV.BBEKMautnerLp.quotient_psi_ergodic
#print axioms VV.BBEKEntropyTrapped.trappedEntropy_pos_of_not_zero_box
#print axioms VV.BBEKDiagonalAverage.averaged_diagonal_ergodic
