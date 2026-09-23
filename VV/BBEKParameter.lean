import VV.BBEKQuotient
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! The lower-unipotent parameter chart is an isometry for the standard
entrywise maximum metric; [0,1] × Z_2 has compact image in the group and
in the actual arithmetic quotient. -/

noncomputable section
open Matrix Metric
open scoped MatrixGroups Topology

namespace VV.BBEKDynamics

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

instance matrix2MetricSpace {K : Type*} [MetricSpace K] : MetricSpace (Matrix (Fin 2) (Fin 2) K) :=
  inferInstanceAs (MetricSpace (Fin 2 → Fin 2 → K))

instance slMetricSpace {K : Type*} [CommRing K] [MetricSpace K] : MetricSpace SL(2,K) :=
  inferInstanceAs (MetricSpace {M : Matrix (Fin 2) (Fin 2) K // M.det=1})

theorem lower_dist {K : Type*} [CommRing K] [MetricSpace K] (u v : K) :
    dist (lower u) (lower v)=dist u v := by
  change dist (!![1,0;u,1]) (!![1,0;v,1])=dist u v
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [dist_nonneg]
  · exact (dist_le_pi_dist (![u,1]) (![v,1]) 0).trans
      (dist_le_pi_dist (!![1,0;u,1]) (!![1,0;v,1]) 1)

theorem isometry_lower {K : Type*} [CommRing K] [MetricSpace K] :
    Isometry (lower : K → SL(2,K)) := Isometry.of_dist_eq lower_dist

theorem isometry_x : Isometry (fun a : ℝ×Q2 => x a.1 a.2) := by
  apply Isometry.of_dist_eq
  intro a b
  change max (dist (lower a.1) (lower b.1)) (dist (lower a.2) (lower b.2)) =
    max (dist a.1 b.1) (dist a.2 b.2)
  rw [lower_dist,lower_dist]

theorem isEmbedding_x : Topology.IsEmbedding (fun a : ℝ×Q2 => x a.1 a.2) :=
  isometry_x.isEmbedding

def parameterBox : Set (ℝ×Q2) := Set.Icc 0 1 ×ˢ closedBall 0 1

theorem mem_parameterBox (a : ℝ×Q2) : a ∈ parameterBox ↔
    0≤a.1 ∧ a.1≤1 ∧ ‖a.2‖≤1 := by
  simp only [parameterBox,Set.mem_prod,Set.mem_Icc,mem_closedBall,dist_zero_right,and_assoc]

theorem parameterBox_compact : IsCompact parameterBox :=
  isCompact_Icc.prod (isCompact_closedBall 0 1)

def parameterImage : Set G := (fun a : ℝ×Q2 => x a.1 a.2) '' parameterBox

theorem parameterImage_compact : IsCompact parameterImage :=
  parameterBox_compact.image continuous_x

theorem parameterQuotientImage_compact : IsCompact
    ((fun a : ℝ×Q2 => BBEKQuotient.parameterPoint a.1 a.2) '' parameterBox) :=
  parameterBox_compact.image BBEKQuotient.parameterPoint_continuous

end VV.BBEKDynamics
