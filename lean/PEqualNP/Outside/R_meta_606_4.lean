import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.LowMerge

theorem PEqualNP.Outside.R_meta_606_4
    (liftInputs : ∀ (n : ℕ) (D : Circuit), Monotone2 D →
      ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ 3 * (D.size + 1) ∧
        ∀ x y : Fin n → Bool, circuitFun (n + n) C (Fin.append x y) =
          circuitFun n D (fun i => x i || y i))
    (reduceDegree : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (D : Circuit), (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → Monotone2 D →
      (∀ x y : Fin n → Bool, G.IsIndepSet {i | x i = true} → G.IsIndepSet {i | y i = true} →
        (circuitFun (n + n) D (Fin.append x y) = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ y j = true)) →
      ∃ (C : Circuit) (a b : ℕ), Monotone2 C ∧ C.size + 1 ≤ k * (D.size + 1) ∧
        C.gates.getLast? = some ⟨GateOp.and, [a, b]⟩ ∧ C.output + 1 = n + n + C.size ∧
        (C.lineDegrees (n + n) (Finset.Ico n (n + n))).getD a 0 ≤ 2 ∧
        (C.lineDegrees (n + n) (Finset.Ico n (n + n))).getD b 0 ≤ 1 ∧
        (∀ x y : Fin n → Bool, G.IsIndepSet {i | x i = true} → G.IsIndepSet {i | y i = true} →
          circuitFun (n + n) C (Fin.append x y) = true → ∃ i j, G.Adj i j ∧ x i = true ∧ y j = true) ∧
        G.edgeFinset.card ≤ Fintype.card {e : Fin n × Fin n // C.eval (pointLineInput n n e.1 e.2) = true})
    (countProduct : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (a b : ℕ),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → Monotone2 C →
      C.gates.getLast? = some ⟨GateOp.and, [a, b]⟩ → C.output + 1 = n + n + C.size →
      (C.lineDegrees (n + n) (Finset.Ico n (n + n))).getD a 0 ≤ 2 →
      (C.lineDegrees (n + n) (Finset.Ico n (n + n))).getD b 0 ≤ 1 →
      (∀ x y : Fin n → Bool, G.IsIndepSet {i | x i = true} → G.IsIndepSet {i | y i = true} →
        circuitFun (n + n) C (Fin.append x y) = true → ∃ i j, G.Adj i j ∧ x i = true ∧ y j = true) →
      Fintype.card {e : Fin n × Fin n // C.eval (pointLineInput n n e.1 e.2) = true} ≤ k * (C.size + 1)) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨k, hreduce⟩ := reduceDegree
  obtain ⟨b, hcount⟩ := countProduct
  refine ⟨b * k * 3, ?_⟩
  intro n G _ hg D hd hfun
  obtain ⟨H, hm, hs, hval⟩ := liftInputs n D hd
  have hexact (x y : Fin n → Bool) (hx : G.IsIndepSet {i | x i = true})
      (hy : G.IsIndepSet {i | y i = true}) :
      circuitFun (n + n) H (Fin.append x y) = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ y j = true := by
    rw [hval, hfun]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    constructor
    · rintro ⟨i, j, hij, hi | hi, hj | hj⟩
      · exact False.elim (hx hi hj (G.ne_of_adj hij) hij)
      · exact ⟨i, j, hij, hi, hj⟩
      · exact ⟨j, i, hij.symm, hj, hi⟩
      · exact False.elim (hy hi hj (G.ne_of_adj hij) hij)
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨i, j, hij, Or.inl hi, Or.inr hj⟩
  obtain ⟨C, a, c, hcm, hcs, hgate, hout, hda, hdb, hsound, hcover⟩ :=
    hreduce n G H hg hm hexact
  calc
    G.edgeFinset.card ≤ _ := hcover
    _ ≤ b * (C.size + 1) := hcount n G C a c hg hcm hgate hout hda hdb hsound
    _ ≤ b * (k * (H.size + 1)) := Nat.mul_le_mul_left _ hcs
    _ ≤ b * (k * (3 * (D.size + 1))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs)
    _ = b * k * 3 * (D.size + 1) := by simp only [Nat.mul_assoc]
