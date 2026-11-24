import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_1682_8
    (hand :
      let sep := fun a b : Fin 26 => (a.val < 13 ↔ ¬ b.val < 13)
      let e := fun a b : Fin 26 => sep a b ∧
        ((if a.val < 13 then a.val + 26 - b.val else b.val + 26 - a.val) % 13)
          ∈ ({0, 1, 3, 9} : Finset ℕ)
      ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 62 ∧
        (∀ u v : Fin 26, e u v → let x := fun k : Fin 26 => decide (k = u ∨ k = v)
          C.eval (List.ofFn x ++ [(x 0 && x 13), true, false]) = true) ∧
        (∀ x : Fin 26 → Bool,
          (∀ u v, e u v → x u = true → x v = false) →
          (∀ u, x u = false → ∃ v, e u v ∧ x v = true) →
          (∀ u, ∃ v, sep u v ∧ ¬ e u v ∧ x v = true) →
          C.eval (List.ofFn x ++ [(x 0 && x 13), true, false]) = false))
    (horSide :
      let sep := fun a b : Fin 26 => (a.val < 13 ↔ ¬ b.val < 13)
      let e := fun a b : Fin 26 => sep a b ∧
        ((if a.val < 13 then a.val + 26 - b.val else b.val + 26 - a.val) % 13)
          ∈ ({0, 1, 3, 9} : Finset ℕ)
      ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 62 ∧
        (∀ u v : Fin 26, e u v → let x := fun k : Fin 26 => decide (k = u ∨ k = v)
          C.eval (List.ofFn x ++ [(x 0 || x 1), true, false]) = true) ∧
        (∀ x : Fin 26 → Bool,
          (∀ u v, e u v → x u = true → x v = false) →
          (∀ u, x u = false → ∃ v, e u v ∧ x v = true) →
          (∀ u, ∃ v, sep u v ∧ ¬ e u v ∧ x v = true) →
          C.eval (List.ofFn x ++ [(x 0 || x 1), true, false]) = false))
    (horEdge :
      let sep := fun a b : Fin 26 => (a.val < 13 ↔ ¬ b.val < 13)
      let e := fun a b : Fin 26 => sep a b ∧
        ((if a.val < 13 then a.val + 26 - b.val else b.val + 26 - a.val) % 13)
          ∈ ({0, 1, 3, 9} : Finset ℕ)
      ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 62 ∧
        (∀ u v : Fin 26, e u v → let x := fun k : Fin 26 => decide (k = u ∨ k = v)
          C.eval (List.ofFn x ++ [(x 0 || x 13), true, false]) = true) ∧
        (∀ x : Fin 26 → Bool,
          (∀ u v, e u v → x u = true → x v = false) →
          (∀ u, x u = false → ∃ v, e u v ∧ x v = true) →
          (∀ u, ∃ v, sep u v ∧ ¬ e u v ∧ x v = true) →
          C.eval (List.ofFn x ++ [(x 0 || x 13), true, false]) = false))
    (horOther :
      let sep := fun a b : Fin 26 => (a.val < 13 ↔ ¬ b.val < 13)
      let e := fun a b : Fin 26 => sep a b ∧
        ((if a.val < 13 then a.val + 26 - b.val else b.val + 26 - a.val) % 13)
          ∈ ({0, 1, 3, 9} : Finset ℕ)
      ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 62 ∧
        (∀ u v : Fin 26, e u v → let x := fun k : Fin 26 => decide (k = u ∨ k = v)
          C.eval (List.ofFn x ++ [(x 2 || x 13), true, false]) = true) ∧
        (∀ x : Fin 26 → Bool,
          (∀ u v, e u v → x u = true → x v = false) →
          (∀ u, x u = false → ∃ v, e u v ∧ x v = true) →
          (∀ u, ∃ v, sep u v ∧ ¬ e u v ∧ x v = true) →
          C.eval (List.ofFn x ++ [(x 2 || x 13), true, false]) = false)) : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  rintro ⟨C, hm, hs, hpos, hneg⟩
  let sep := fun a b : Fin 26 => (a.val < 13 ↔ ¬ b.val < 13)
  let e := fun a b : Fin 26 => sep a b ∧
    ((if a.val < 13 then a.val + 26 - b.val else b.val + 26 - a.val) % 13)
      ∈ ({0, 1, 3, 9} : Finset ℕ)
  let pos := fun u v : Fin 26 => fun k : Fin 26 => decide (k = u ∨ k = v)
  let neg := fun x : Fin 26 → Bool =>
    (∀ u v, e u v → x u = true → x v = false) ∧
    (∀ u, x u = false → ∃ v, e u v ∧ x v = true) ∧
    (∀ u, ∃ v, sep u v ∧ ¬ e u v ∧ x v = true)
  let inc := fun p w : Fin 13 => ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd
  let pt := Fin.castAdd 13 (n := 13)
  let ln := Fin.natAdd 13 (m := 13)
  have sepPP : ∀ p q, ¬ sep (pt p) (pt q) := by decide
  have sepLL : ∀ w z, ¬ sep (ln w) (ln z) := by decide
  have edgePL : ∀ p w, e (pt p) (ln w) ↔ inc p w := by decide
  have edgeLP : ∀ p w, e (ln w) (pt p) ↔ inc p w := by decide
  have edgeSym : ∀ a b, e a b ↔ e b a := by decide
  have posSym (a b) : pos a b = pos b a := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [pos, decide_eq_true_eq]
    exact or_comm
  have cases26 (motive : Fin 26 → Prop) (a : ∀ p, motive (pt p))
      (b : ∀ w, motive (ln w)) : ∀ k, motive k :=
    Fin.addCases (m := 13) (n := 13) (motive := motive) a b
  have Cpos : ∀ u v, e u v → C.eval (List.ofFn (pos u v)) = true := by
    apply cases26
    · intro p
      apply cases26
      · exact fun q h => (sepPP p q h.1).elim
      · exact fun w h => hpos p w ((edgePL p w).1 h)
    · intro w
      apply cases26
      · intro p h
        rw [posSym]
        exact hpos p w ((edgeLP p w).1 h)
      · exact fun z h => (sepLL w z h.1).elim
  have Cneg : ∀ x, neg x → C.eval (List.ofFn x) = false := by
    rintro x ⟨hind, hmax, hgen⟩
    let P : Finset (Fin 13) := Finset.univ.filter fun p => x (pt p) = true
    have mP (p) : p ∈ P ↔ x (pt p) = true := by simp [P]
    have oppP (w) : ∀ i, sep (ln w) i → ∃ q, i = pt q := by
      apply cases26
      · exact fun q _ => ⟨q, rfl⟩
      · exact fun z h => (sepLL w z h).elim
    have oppL (p) : ∀ i, sep (pt p) i → ∃ w, i = ln w := by
      apply cases26
      · exact fun q h => (sepPP p q h).elim
      · exact fun w _ => ⟨w, rfl⟩
    have mL (w) : x (ln w) = true ↔ ∀ p ∈ P, ¬ inc p w := by
      constructor
      · intro hx p hp hi
        exact Bool.false_ne_true ((hind _ _ ((edgePL p w).2 hi) ((mP p).1 hp)).symm.trans hx)
      · intro h
        cases hx : x (ln w) with
        | true => rfl
        | false =>
          obtain ⟨i, hi, hxi⟩ := hmax _ hx
          obtain ⟨p, rfl⟩ := oppP w i hi.1
          exact False.elim (h p ((mP p).2 hxi) ((edgeLP p w).1 hi))
    have hPmax : ∀ p, p ∉ P → ∃ w, (∀ q ∈ P, ¬ inc q w) ∧ inc p w := by
      intro p hp
      have hx : x (pt p) = false := by simpa using mt (mP p).2 hp
      obtain ⟨i, hi, hxi⟩ := hmax _ hx
      obtain ⟨w, rfl⟩ := oppL p i hi.1
      exact ⟨w, (mL w).1 hxi, (edgePL p w).1 hi⟩
    have hPgen : (¬ ∃ w, ∀ p ∈ P, inc p w) ∧
        (¬ ∃ p, ∀ w, (∀ q ∈ P, ¬ inc q w) → inc p w) := by
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨i, hi, hni, hxi⟩ := hgen (ln w)
        obtain ⟨p, rfl⟩ := oppP w i hi
        exact hni ((edgeLP p w).2 (hw p ((mP p).2 hxi)))
      · rintro ⟨p, hp⟩
        obtain ⟨i, hi, hni, hxi⟩ := hgen (pt p)
        obtain ⟨w, rfl⟩ := oppL p i hi
        exact hni ((edgePL p w).2 (hp w ((mL w).1 hxi)))
    have ptInj : ∀ p q, pt p = pt q ↔ p = q := by decide
    have lnInj : ∀ w z, ln w = ln z ↔ w = z := by decide
    have cross : ∀ p w, pt p ≠ ln w := by decide
    let y : Fin (13 + 13) → Bool := fun kk =>
      decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
        (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
          (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))
    have hy : circuitFun (13 + 13) C y = false :=
      hneg P hPmax hPgen
    have hx : x = y := by
      funext k
      apply Bool.eq_iff_iff.mpr
      simp only [y, decide_eq_true_eq]
      change (x k = true ↔ ((∃ p ∈ P, k = pt p) ∨
        (∃ w, k = ln w ∧ ∀ p ∈ P, ¬ inc p w)))
      revert k
      apply cases26
      · intro p
        constructor
        · intro hp
          exact Or.inl ⟨p, (mP p).2 hp, rfl⟩
        · rintro (⟨q, hq, he⟩ | ⟨w, hw, _⟩)
          · obtain rfl := (ptInj p q).1 he
            exact (mP p).1 hq
          · exact (cross p w hw).elim
      · intro w
        constructor
        · intro hw
          exact Or.inr ⟨w, rfl, (mL w).1 hw⟩
        · rintro (⟨p, _, hp⟩ | ⟨z, hz, h⟩)
          · exact (cross p w hp.symm).elim
          · obtain rfl := (lnInj w z).1 hz
            exact (mL w).2 h
    change circuitFun (13 + 13) C x = false
    rw [hx]
    exact hy
  -- The generators preserve incidence and may exchange points with lines.
  let gens : Fin 4 → Fin 26 → Fin 26 := ![![13, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 13], ![0, 2, 3, 8, 5, 7, 6, 4, 9, 12, 11, 10, 1, 25, 15, 20, 18, 17, 19, 16, 21, 22, 24, 23, 14, 13], ![0, 2, 4, 8, 10, 11, 3, 6, 5, 12, 1, 9, 7, 25, 14, 21, 20, 23, 15, 16, 18, 22, 24, 13, 19, 17]]
  -- Read each word from its least significant base-five digit.
  let preword : Fin 26 → ℕ := ![0, 122070312, 24414062, 4882812, 976562, 195312, 39062, 7812, 1562, 312, 62, 12, 2, 1, 11, 61, 311, 1561, 7811, 39061, 195311, 976561, 4882811, 24414061, 122070311, 610351561]
  let classword : Fin 26 → ℕ := ![0, 0, 124, 468, 24, 119, 2344, 123, 93, 18, 4, 23, 3, 0, 7973, 1594, 7969, 24, 7974, 39848, 1593, 318, 63, 4, 12, 3]
  let ren : ℕ → ℕ → Fin 26 → Fin 26 := fun fuel =>
    Nat.rec (fun _ i => i) (fun _ go code i =>
      if code = 0 then i else go (code / 5) (gens ⟨(code % 5 + 3) % 4, Nat.mod_lt _ (by decide)⟩ i)) fuel
  let good := fun s : Fin 26 → Fin 26 =>
    Function.Bijective s ∧ (∀ u v, e (s u) (s v) ↔ e u v) ∧ (∀ u v, sep (s u) (s v) ↔ sep u v)
  have goodGens : ∀ j, good (gens j) := by
    change ∀ j, ((∀ a b, gens j a = gens j b → a = b) ∧ (∀ b, ∃ a, gens j a = b)) ∧
      (∀ u v, e (gens j u) (gens j v) ↔ e u v) ∧
      (∀ u v, sep (gens j u) (gens j v) ↔ sep u v)
    decide
  have goodRen : ∀ fuel code, good (ren fuel code) := by
    intro fuel
    induction fuel with
    | zero => intro code; exact ⟨Function.bijective_id, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
    | succ fuel ih =>
      intro code
      by_cases hc : code = 0
      · have eq : ren (fuel + 1) code = id := by
          subst code
          rfl
        rw [eq]
        exact ⟨Function.bijective_id, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
      · let j : Fin 4 := ⟨(code % 5 + 3) % 4, Nat.mod_lt _ (by decide)⟩
        have eq : ren (fuel + 1) code = ren fuel (code / 5) ∘ gens j := by
          funext i
          change (if code = 0 then i else ren fuel (code / 5) (gens j i)) =
            ren fuel (code / 5) (gens j i)
          rw [ite_eq_right hc]
        rw [eq]
        obtain ⟨hb, he, hp⟩ := ih (code / 5)
        obtain ⟨hb', he', hp'⟩ := goodGens j
        exact ⟨hb.comp hb', fun a b => (he _ _).trans (he' _ _), fun a b => (hp _ _).trans (hp' _ _)⟩
  let isPair := fun (a b u v : Fin 26) => (a = u ∧ b = v) ∨ (a = v ∧ b = u)
  let pre := fun a : Fin 26 => ren 13 (preword a)
  let finish := fun b : Fin 26 => ren 9 (classword b)
  let perm := fun a b => finish (pre a b) ∘ pre a
  have goodPerm (a b) : good (perm a b) := by
    obtain ⟨hb, he, hp⟩ := goodRen 13 (preword a)
    obtain ⟨hb', he', hp'⟩ := goodRen 9 (classword (pre a b))
    exact ⟨hb'.comp hb, fun u v => (he' _ _).trans (he _ _), fun u v => (hp' _ _).trans (hp _ _)⟩
  have preZero : ∀ a, pre a a = 0 := by decide
  have anchors : ∀ b : Fin 26, b ≠ 0 →
      isPair (finish b 0) (finish b b) 0 1 ∨
      isPair (finish b 0) (finish b b) 0 13 ∨ isPair (finish b 0) (finish b b) 2 13 := by decide
  have pairs (a b : Fin 26) (hab : a ≠ b) :
      isPair (perm a b a) (perm a b b) 0 1 ∨
      isPair (perm a b a) (perm a b b) 0 13 ∨ isPair (perm a b a) (perm a b b) 2 13 := by
    have hne : pre a b ≠ 0 := by
      rw [← preZero a]
      exact fun h => hab ((goodRen 13 (preword a)).1.1 h).symm
    simpa only [perm, Function.comp_apply, preZero] using anchors (pre a b) hne
  have onlyEdge : ¬ e 0 1 ∧ e 0 13 ∧ ¬ e 2 13 := by decide
  let feature : Fin 4 → (Fin 26 → Bool) → Bool :=
    ![fun x => x 0 && x 13, fun x => x 0 || x 1, fun x => x 0 || x 13, fun x => x 2 || x 13]
  -- The extra wires are the fixed first gate and the two Boolean constants.
  let liftInput := fun (k : Fin 4) (x : Fin 26 → Bool) =>
    List.ofFn x ++ [feature k x, true, false]
  have noTail (k : Fin 4) (D : Circuit) (hD : Monotone2 D) (hsD : D.size ≤ 62)
      (hpD : ∀ u v, e u v → D.eval (liftInput k (pos u v)) = true)
      (hnD : ∀ x, neg x → D.eval (liftInput k x) = false) : False := by
    fin_cases k
    · exact hand ⟨D, hD, hsD, hpD, fun x a b c => hnD x ⟨a, b, c⟩⟩
    · exact horSide ⟨D, hD, hsD, hpD, fun x a b c => hnD x ⟨a, b, c⟩⟩
    · exact horEdge ⟨D, hD, hsD, hpD, fun x a b c => hnD x ⟨a, b, c⟩⟩
    · exact horOther ⟨D, hD, hsD, hpD, fun x a b c => hnD x ⟨a, b, c⟩⟩
  have getInput (x : Fin 26 → Bool) (i : ℕ) :
      (List.ofFn x).getD i false = if h : i < 26 then x ⟨i, h⟩ else false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split <;> rfl
  have getLift (k : Fin 4) (x : Fin 26 → Bool) (i : ℕ) :
      (liftInput k x).getD i false =
        if h : i < 26 then x ⟨i, h⟩ else if i = 26 then feature k x else decide (i = 27) := by
    change (List.ofFn x ++ [feature k x, true, false]).getD i false = _
    by_cases h : i < 26
    · rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using h), getInput]
      simp only [dite_eq_left h]
    · rw [List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt h)]
      simp only [List.length_ofFn, dite_eq_right h]
      by_cases hi : i ≤ 28
      · interval_cases i <;> rfl
      · have hi' : 29 ≤ i := Nat.lt_of_not_ge hi
        have hn : [feature k x, true, false].length ≤ i - 26 := Nat.le_sub_of_add_le hi'
        rw [List.getD_eq_default _ _ hn]
        have h26 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 26 < 29) hi')
        have h27 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 27 < 29) hi')
        simp [h26, h27]
  have getSnoc (l : List Bool) (v : Bool) (i : ℕ) :
      (l ++ [v]).getD i false = if i = l.length then v else l.getD i false := by
    by_cases h : i < l.length
    · rw [List.getD_append _ _ _ _ h, ite_eq_right (Nat.ne_of_lt h)]
    · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)]
      by_cases he : i = l.length
      · simp [he]
      · have hi : l.length < i := lt_of_le_of_ne (Nat.le_of_not_gt h) (Ne.symm he)
        have hsub : [v].length ≤ i - l.length := Nat.le_sub_of_add_le' hi
        rw [ite_eq_right he, List.getD_eq_default _ _ hsub,
          List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
  have shortList (l : List ℕ) (hlen : l.length ≤ 2) :
      l = [] ∨ (∃ i, l = [i]) ∨ ∃ i j, l = [i, j] := by
    rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, ls⟩⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, j, rfl⟩)
    · simp at hlen
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  let step := fun (l : List Bool) (g : Gate) =>
    l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]
  let ok := fun (g : Gate) =>
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  -- Relabel original inputs, replace the first gate, and shift each later wire by two.
  have transTail (s : Fin 26 → Fin 26) (r : ℕ) (hr : r < 29) :
      let idx := fun i : ℕ => if h : i < 26 then (s ⟨i, h⟩).val else if i = 26 then r else i + 2
      let mapGate := fun g : Gate => Gate.mk g.op (g.inputs.map idx)
      ∀ (gs : List Gate), (∀ g ∈ gs, ok g) → ∀ (a b : List Bool),
        27 ≤ a.length → b.length = a.length + 2 →
        ∀ (R : Bool → Bool → Prop),
        (∀ a₁ a₂ b₁ b₂, R a₁ b₁ → R a₂ b₂ →
           R (a₁ && a₂) (b₁ && b₂) ∧ R (a₁ || a₂) (b₁ || b₂)) →
        (∀ v, R v v) →
        (∀ i, R (a.getD i false) (b.getD (idx i) false)) →
        ∀ i, R ((gs.foldl step a).getD i false) (((gs.map mapGate).foldl step b).getD (idx i) false) := by
    dsimp only
    intro gs hg a b ha hb R hgate hdiag hab i
    induction gs generalizing a b with
    | nil => exact hab i
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih (fun g hg' => hg g (List.mem_cons_of_mem _ hg'))
        _ _ (by simpa [step] using Nat.le_trans ha (Nat.le_succ a.length))
        (by simpa [step] using hb)
      intro j
      have hj : (if h : j < 26 then (s ⟨j, h⟩).val else if j = 26 then r else j + 2)
          = b.length ↔ j = a.length := by
        have hlen : 29 ≤ b.length := by
          rw [hb]
          exact Nat.add_le_add_right ha 2
        have ha26 : 26 < a.length := ha
        by_cases h : j < 26
        · rw [dite_eq_left h]
          have hwire := Nat.lt_trans (s ⟨j, h⟩).isLt
            (Nat.lt_of_lt_of_le (by decide : 26 < 29) hlen)
          exact iff_of_false (Nat.ne_of_lt hwire) (Nat.ne_of_lt (Nat.lt_trans h ha26))
        · rw [dite_eq_right h]
          by_cases hj26 : j = 26
          · rw [ite_eq_left hj26, hj26]
            exact iff_of_false (Nat.ne_of_lt (Nat.lt_of_lt_of_le hr hlen)) (Nat.ne_of_lt ha26)
          · rw [ite_eq_right hj26, hb]
            exact Nat.add_right_cancel_iff
      simp only [step, getSnoc, hj]
      split
      · obtain ⟨hgo, hgi⟩ := hg g (List.mem_cons_self ..)
        rcases g with ⟨op, l⟩
        change op = GateOp.and ∨ op = GateOp.or at hgo
        change l.length ≤ 2 at hgi
        obtain hnil | ⟨u, hu⟩ | ⟨u, v, huv⟩ := shortList l hgi
        · subst l
          rcases hgo with rfl | rfl
          · exact hdiag true
          · exact hdiag false
        · subst l
          rcases hgo with rfl | rfl
          · simpa [evalAnd] using hab u
          · simpa [evalOr] using hab u
        · subst l
          rcases hgo with rfl | rfl
          · simpa [evalAnd] using (hgate _ _ _ _ (hab u) (hab v)).1
          · simpa [evalOr] using (hgate _ _ _ _ (hab u) (hab v)).2
      · exact hab j
  have negRen (s : Fin 26 → Fin 26) (h : good s) (x : Fin 26 → Bool)
      (hx : neg x) : neg (x ∘ s) := by
    obtain ⟨hbij, he, hp⟩ := h
    obtain ⟨hind, hmax, hgen⟩ := hx
    refine ⟨fun a b h hxa => hind (s a) (s b) ((he a b).2 h) hxa, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb, hxb⟩ := hmax (s a) ha
      obtain ⟨i, rfl⟩ := hbij.2 b
      exact ⟨i, (he a i).1 hb, hxb⟩
    · intro a
      obtain ⟨b, hb, hnb, hxb⟩ := hgen (s a)
      obtain ⟨i, rfl⟩ := hbij.2 b
      exact ⟨i, (hp a i).1 hb, fun h => hnb ((he a i).2 h), hxb⟩
  let first := fun (g : Gate) (x : Fin 26 → Bool) =>
    g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
  have posRen (s : Fin 26 → Fin 26) (h : good s)
      (u v : Fin 26) (he : e u v) :
      C.eval (List.ofFn (pos u v ∘ s)) = true := by
    obtain ⟨a, rfl⟩ := h.1.2 u
    obtain ⟨b, rfl⟩ := h.1.2 v
    have hx : pos (s a) (s b) ∘ s = pos a b := by
      funext i
      simp [pos, h.1.1.eq_iff]
    rw [hx]
    exact Cpos a b ((h.2.1 a b).1 he)
  have process (g : Gate) (gs : List Gate) (hgs : C.gates = g :: gs)
      (s : Fin 26 → Fin 26) (hsg : good s) (k : Fin 4) (r : ℕ) (hr : r < 29)
      (hp : ∀ u v, e u v →
        first g (pos u v ∘ s) = true → (liftInput k (pos u v)).getD r false = true)
      (hn : ∀ x, neg x →
        (liftInput k x).getD r false = true → first g (x ∘ s) = true) : False := by
    let idx := fun i : ℕ => if h : i < 26 then (s ⟨i, h⟩).val else if i = 26 then r else i + 2
    let D : Circuit := ⟨gs.map (fun g => ⟨g.op, g.inputs.map idx⟩), idx C.output⟩
    have HG : ∀ g' ∈ gs, ok g' := by
      intro g' hg'
      apply hm
      rw [hgs]
      exact List.mem_cons_of_mem _ hg'
    have hD : Monotone2 D := by
      intro q hq
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hq
      exact ⟨(HG _ hg').1, by simpa using (HG _ hg').2⟩
    have hDsize : D.size ≤ 62 := by
      change C.gates.length ≤ 63 at hs
      rw [hgs, List.length_cons] at hs
      change (gs.map (fun g => Gate.mk g.op (g.inputs.map idx))).length ≤ 62
      rw [List.length_map]
      exact Nat.le_of_succ_le_succ hs
    let R := fun (dir a b : Bool) =>
      if dir then a = true → b = true else b = true → a = true
    have relGate (d : Bool) (a₁ a₂ b₁ b₂ : Bool) (h₁ : R d a₁ b₁) (h₂ : R d a₂ b₂) :
        R d (a₁ && a₂) (b₁ && b₂) ∧ R d (a₁ || a₂) (b₁ || b₂) := by
      cases d <;> simp only [R, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true] at *
      all_goals tauto
    have relDiag (d b : Bool) : R d b b := by cases d <;> simp [R]
    have both (x : Fin 26 → Bool) (d : Bool)
        (hfirst : R d (first g (x ∘ s)) ((liftInput k x).getD r false)) :
        R d (C.eval (List.ofFn (x ∘ s))) (D.eval (liftInput k x)) := by
      let a := step (List.ofFn (x ∘ s)) g
      let b := liftInput k x
      have ha : a.length = 27 := by simp [a, step]
      have hb : b.length = 29 := by simp [b, liftInput]
      have hbase : ∀ i, R d (a.getD i false) (b.getD (idx i) false) := by
        intro i
        change R d ((List.ofFn (x ∘ s) ++ [first g (x ∘ s)]).getD i false) _
        rw [getSnoc, List.length_ofFn]
        by_cases hi : i < 26
        · have hi' := (s ⟨i, hi⟩).isLt
          simp only [ite_eq_right (Nat.ne_of_lt hi), getInput, getLift, idx, b,
            dite_eq_left hi, dite_eq_left hi', Function.comp_apply]
          exact relDiag _ _
        · by_cases heq : i = 26
          · subst i
            simpa [idx, b] using hfirst
          · have h27 : 27 < i + 2 :=
              Nat.lt_of_lt_of_le (by decide : 27 < 28) (Nat.add_le_add_right (Nat.le_of_not_gt hi) 2)
            have h26 := Nat.lt_trans (by decide : 26 < 27) h27
            simp only [ite_eq_right heq, getInput, getLift, idx, b, dite_eq_right hi,
              dite_eq_right (Nat.not_lt_of_ge (Nat.le_of_lt h26)),
              ite_eq_right (Nat.ne_of_gt h26), Nat.ne_of_gt h27, decide_false]
            exact relDiag _ _
      have hrel := transTail s r hr gs HG a b (by simpa only [ha] using Nat.le_refl 27) (by rw [ha, hb])
        (R d) (relGate d) (relDiag d) hbase C.output
      change R d ((C.gates.foldl step (List.ofFn (x ∘ s))).getD C.output false)
        (((gs.map (fun g => Gate.mk g.op (g.inputs.map idx))).foldl step b).getD (idx C.output) false)
      rw [hgs, List.foldl_cons]
      exact hrel
    apply noTail k D hD hDsize
    · intro u v hu
      have h := both (pos u v) true (hp u v hu)
      exact h (posRen s hsg u v hu)
    · intro x hx
      have h := both x false (hn x hx)
      cases hv : D.eval (liftInput k x)
      · rfl
      · exact Bool.noConfusion ((Cneg (x ∘ s) (negRen s hsg x hx)).symm.trans (h hv))
  cases hgs : C.gates with
  | nil =>
    have ha := Cpos 0 13 (by decide)
    have hb := Cpos 1 14 (by decide)
    have readOnly (x : Fin 26 → Bool) : C.eval (List.ofFn x) = (List.ofFn x).getD C.output false := by
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
      rw [hgs, List.foldl_nil]
    rw [readOnly, getInput] at ha hb
    by_cases hi : C.output < 26
    · rw [dite_eq_left hi] at ha hb
      have hfalse : ∀ i : Fin 26, pos 0 13 i = true → pos 1 14 i = false := by decide
      exact Bool.false_ne_true ((hfalse _ ha).symm.trans hb)
    · simp [hi] at ha
  | cons g gs =>
    have hgm : ok g := hm g (by simp [hgs])
    have goodId : good id :=
      ⟨Function.bijective_id, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
    have useEq (s : Fin 26 → Fin 26) (h : good s) (k : Fin 4) (r : ℕ) (hr : r < 29)
        (hf : ∀ x, first g (x ∘ s) = (liftInput k x).getD r false) : False :=
      process g gs hgs s h k r hr
        (fun u v _ hv => (hf _).symm.trans hv) (fun x _ hv => (hf _).trans hv)
    obtain ⟨hop, hcap⟩ := hgm
    change g.op = GateOp.and ∨ g.op = GateOp.or at hop
    have opForm : ∃ o : Bool, g.op = (if o then GateOp.or else GateOp.and) := by
      rcases hop with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨o, ho⟩ := opForm
    let src := fun i : ℕ => if i < 26 then i else 28
    have hr (i) : src i < 29 := by
      by_cases hi : i < 26
      · simpa only [src, ite_eq_left hi] using Nat.lt_trans hi (by decide : 26 < 29)
      · simpa only [src, ite_eq_right hi] using (by decide : 28 < 29)
    have readAlias (x : Fin 26 → Bool) (i : ℕ) :
        (liftInput 0 x).getD (src i) false = (List.ofFn x).getD i false := by
      rw [getInput]
      by_cases hi : i < 26
      · rw [show src i = i by simp [src, hi], getLift]
        simp only [dite_eq_left hi]
      · rw [show src i = 28 by simp [src, hi], getLift, dite_eq_right hi]
        rfl
    let mix := fun (a b : Bool) => if o then a || b else a && b
    have comm (a b) : mix a b = mix b a := by cases o <;> simp [mix, Bool.and_comm, Bool.or_comm]
    have bothSame (a) : mix a a = a := by cases o <;> simp [mix]
    have first2 (i j : ℕ) (h : g.inputs = [i, j]) (x : Fin 26 → Bool) :
        first g x = mix ((List.ofFn x).getD i false) ((List.ofFn x).getD j false) := by
      simp only [first, h, List.map_cons, List.map_nil, ho]
      cases o
      · simp [mix, evalAnd]
      · simp [mix, evalOr]
    have anyPair (i j) (hi : i < 26) (hj : j < 26) (hin : g.inputs = [i, j]) :
        ∀ (s : Fin 26 → Fin 26) (x : Fin 26 → Bool),
          first g (x ∘ s) = mix (x (s ⟨i, hi⟩)) (x (s ⟨j, hj⟩)) := by
      intro s x
      simp only [first2 _ _ hin, getInput, dite_eq_left hi, dite_eq_left hj, Function.comp_apply]
    have andUnlessEdge (a b : Fin 26) (hn : a ≠ b) (hnb : ¬ e a b) :
        ∀ u v, e u v → ¬ (pos u v a = true ∧ pos u v b = true) := by
      rintro u v h ⟨ha, hb⟩
      simp only [pos, decide_eq_true_eq] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hn rfl
      · exact hnb h
      · exact hnb ((edgeSym _ _).1 h)
      · exact hn rfl
    cases hin : g.inputs with
    | nil =>
      cases o
      · apply useEq id goodId 0 27 (by decide)
        intro x
        rw [getLift]
        simp [first, hin, ho, evalAnd]
      · apply useEq id goodId 0 28 (by decide)
        intro x
        rw [getLift]
        simp [first, hin, ho, evalOr]
    | cons i rest =>
      cases rest with
      | nil =>
        apply useEq id goodId 0 (src i) (hr i)
        intro x
        rw [readAlias]
        cases o
        · simp [first, hin, ho, evalAnd]
        · simp [first, hin, ho, evalOr]
      | cons j rest =>
        cases rest with
        | cons v vs => simp [hin] at hcap
        | nil =>
          by_cases heq : i = j
          · subst j
            apply useEq id goodId 0 (src i) (hr i)
            intro x
            rw [readAlias, first2 _ _ hin]
            exact bothSame _
          by_cases hi : i < 26
          · by_cases hj : j < 26
            · let a : Fin 26 := ⟨i, hi⟩
              let b : Fin 26 := ⟨j, hj⟩
              have hab : a ≠ b := fun h => heq (congrArg Fin.val h)
              let s := perm a b
              have hsg : good s := goodPerm a b
              have hpair := pairs a b hab
              have usePair (c d : Fin 26) (k : Fin 4) (hp : isPair (s a) (s b) c d)
                  (hf : ∀ x, mix (x c) (x d) = feature k x) : False := by
                apply useEq s hsg k 26 (by decide)
                intro x
                rw [anyPair i j hi hj hin, getLift, dite_eq_right (by decide : ¬ 26 < 26), ite_eq_left rfl]
                change mix (x (s a)) (x (s b)) = feature k x
                rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
                · rw [ha, hb, hf]
                · rw [ha, hb, comm, hf]
              cases o
              · by_cases hE : e a b
                · have hsE := (hsg.2.1 a b).2 hE
                  have hpEdge (c d : Fin 26) (hp : isPair (s a) (s b) c d) : e c d := by
                    rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
                    · simpa only [ha, hb] using hsE
                    · exact (edgeSym _ _).1 (by simpa only [ha, hb] using hsE)
                  rcases hpair with hp | hp | hp
                  · exact onlyEdge.1 (hpEdge _ _ hp)
                  · exact usePair 0 13 0 hp (fun _ => rfl)
                  · exact onlyEdge.2.2 (hpEdge _ _ hp)
                -- This AND vanishes on positive pairs, so setting it to false preserves the tests.
                · apply process g gs hgs id goodId 0 28 (by decide)
                  · intro u v he h
                    rw [anyPair i j hi hj hin] at h
                    exact (andUnlessEdge a b hab hE u v he (Bool.and_eq_true_iff.mp h)).elim
                  · intro x _ h
                    rw [getLift] at h
                    simp at h
              · rcases hpair with hp | hp | hp
                · exact usePair 0 1 1 hp (fun _ => rfl)
                · exact usePair 0 13 2 hp (fun _ => rfl)
                · exact usePair 2 13 3 hp (fun _ => rfl)
            · cases o
              · apply useEq id goodId 0 28 (by decide)
                intro x
                rw [first2 _ _ hin, getLift, getInput, getInput]
                simp [hi, hj, mix]
              · apply useEq id goodId 0 (src i) (hr i)
                intro x
                rw [first2 _ _ hin, readAlias, getInput (x ∘ id) j, dite_eq_right hj]
                simp [mix]
          · cases o
            · apply useEq id goodId 0 28 (by decide)
              intro x
              rw [first2 _ _ hin, getLift, getInput, dite_eq_right hi]
              simp [mix]
            · apply useEq id goodId 0 (src j) (hr j)
              intro x
              rw [first2 _ _ hin, readAlias, getInput (x ∘ id) i, dite_eq_right hi]
              simp [mix]
