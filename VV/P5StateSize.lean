import VV.P5Window

/-! Exact symbolic sizes; no graph or rank function is enumerated. -/

namespace VV.P5StateSize
open P5Synchronize P5Machine P5Window

theorem card_stateAt (V : Type) [Fintype V] (r : ℕ) :
    Fintype.card (StateAt V r) = Fintype.card V ^ (3 ^ r) := by
  induction r with
  | zero => simp [StateAt]
  | succ r ih =>
    change Fintype.card (StateAt V r × StateAt V r × StateAt V r) = _
    rw [Fintype.card_prod, Fintype.card_prod, ih, pow_succ, pow_mul]
    ring

theorem windowGraph_size (C r : ℕ) :
    (windowGraph C r).size = C * (24 * C ^ 2) ^ (3 ^ r) := by
  change Fintype.card (StateAt (Pair C) r × Fin C) = _
  rw [Fintype.card_prod, Fintype.card_fin, card_stateAt, card_pair]
  exact Nat.mul_comm _ _

theorem windowGraph_ten_fourteen_size :
    (windowGraph 10 14).size = 10 * 2400 ^ 4782969 := by
  have hb : (24 * 10 ^ 2 : ℕ) = 2400 := by decide
  have he : (3 ^ 14 : ℕ) = 4782969 := by decide
  rw [windowGraph_size, hb, he]

/-- The number of candidates in the current existential rank-function search. -/
theorem rankFunctionCount (G : P5Graph.Graph) :
    Fintype.card (Fin G.size → Fin (G.size + 1)) = (G.size + 1) ^ G.size := by
  simp

end VV.P5StateSize
