import FormalConjectures.Paper.TuDengConjecture
import Mathlib

-- Problem: Tu-Deng Conjecture
-- Upstream: formal-conjectures FormalConjectures/Paper/TuDengConjecture.lean (declaration TuDengConjecture.tu_deng_conjecture)
-- Credit: @BetAdmin237 (the owner of the agent is credited as the solver)
-- Mathematics and formalization: the count form of the bound is the Lean development by
-- ifeelok92 (github.com/ifeelok92/tu-deng-conjecture-lean-formal-proof, commit 3c005614,
-- theorem TuDeng.FirstExit.tu_deng_conjecture_full), cited as [Lean26] upstream, following the
-- proofs of Liu, Luo and Xie [LLX26] and Cusick [Cu26]. Ported to this toolchain, merged into
-- one file, comments removed, plus a bridge from residue pairs to the natural-number count.

section
namespace TuDeng
def modulus (k : ℕ) : ℕ :=
  2 ^ k - 1
def hammingWeight (k n : ℕ) : ℕ :=
  ((List.range k).map (fun i => if Nat.testBit n i then 1 else 0)).sum
def partner (k t x : ℕ) : ℕ :=
  (t + modulus k - x) % modulus k
def tuDengCount (k t : ℕ) : ℕ :=
  ((List.range (modulus k)).filter (fun x =>
    hammingWeight k x + hammingWeight k (partner k t x) ≤ k - 1)).length
def TuDengConjecture (k t : ℕ) : Prop :=
  0 < t → t < modulus k → tuDengCount k t ≤ 2 ^ (k - 1)
end TuDeng
end
section
namespace TuDeng.FirstExit
open scoped BigOperators
abbrev Word := List Bool
def zeros (w : Word) : ℕ := w.count false
def ones (w : Word) : ℕ := w.count true
theorem zeros_add_ones (w : Word) : zeros w + ones w = w.length := by
  exact List.count_false_add_count_true w
def LexLT : Word → Word → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs =>
      if a = b then LexLT as bs else a = false ∧ b = true
@[simp] theorem lex_nil_nil : ¬ LexLT [] [] := by simp [LexLT]
@[simp] theorem lex_nil_cons (b : Bool) (v : Word) : LexLT [] (b :: v) := by simp [LexLT]
@[simp] theorem not_lex_cons_nil (b : Bool) (v : Word) : ¬ LexLT (b :: v) [] := by simp [LexLT]
@[simp] theorem lex_cons_same (b : Bool) (u v : Word) :
    LexLT (b :: u) (b :: v) ↔ LexLT u v := by simp [LexLT]
@[simp] theorem lex_false_true (u v : Word) : LexLT (false :: u) (true :: v) := by
  simp [LexLT]
@[simp] theorem not_lex_true_false (u v : Word) : ¬ LexLT (true :: u) (false :: v) := by
  simp [LexLT]
theorem lex_trans : ∀ {u v w : Word}, LexLT u v → LexLT v w → LexLT u w := by
  intro u v w huv hvw
  induction u generalizing v w with
  | nil => cases v <;> cases w <;> simp_all [LexLT]
  | cons a u ih =>
      cases v with
      | nil => simp_all [LexLT]
      | cons b v =>
          cases w with
          | nil => simp_all [LexLT]
          | cons c w =>
              by_cases hab : a = b
              · subst b
                by_cases hbc : a = c
                · subst c
                  simp only [lex_cons_same] at huv hvw ⊢
                  exact ih huv hvw
                · have hac : a ≠ c := hbc
                  simp only [LexLT, if_pos rfl] at huv
                  simp only [LexLT, if_neg hac] at hvw ⊢
                  exact hvw
              · have hab' : a ≠ b := hab
                simp only [LexLT, if_neg hab'] at huv
                rcases huv with ⟨rfl, rfl⟩
                cases c <;> simp_all [LexLT]
theorem lex_prefix (a u v : Word) (h : LexLT u v) :
    LexLT (a ++ u) (a ++ v) := by
  induction a with
  | nil => simpa
  | cons b a ih => simpa using ih
theorem lex_lt_true_cons : ∀ s : Word, LexLT s (true :: s)
  | [] => by simp
  | false :: s => by simp
  | true :: s => by simpa using lex_lt_true_cons s
theorem lex_delete_true (w : Word) (i : ℕ) (hi : i < w.length)
    (hbit : w[i] = true) : LexLT (w.eraseIdx i) w := by
  have htail : LexLT (w.drop (i + 1)) (true :: w.drop (i + 1)) :=
    lex_lt_true_cons _
  have hdrop : w.drop i = true :: w.drop (i + 1) := by
    simpa [hbit] using (List.drop_eq_getElem_cons hi)
  have hw : w.take i ++ (true :: w.drop (i + 1)) = w := by
    rw [← hdrop, List.take_append_drop]
  rw [List.eraseIdx_eq_take_drop_succ]
  simpa only [hw] using lex_prefix (w.take i) _ _ htail
def BoundaryOne (v y : Word) : Prop :=
  ∃ u, u.Sublist v ∧ ¬ y.Sublist v ∧ y = u ++ [true]
def Lang (v y : Word) : Prop :=
  y.Sublist v ∨ (BoundaryOne v y ∧ LexLT y v)
theorem lang_of_sublist {v y : Word} (h : y.Sublist v) : Lang v y := Or.inl h
theorem boundaryOne_append {v u : Word} (hu : u.Sublist v)
    (hnot : ¬ (u ++ [true]).Sublist v) : BoundaryOne v (u ++ [true]) := by
  exact ⟨u, hu, hnot, rfl⟩
theorem lang_eraseIdx_true {v y : Word} (hy : Lang v y) (i : ℕ)
    (hi : i < y.length) (hbit : y[i] = true) : Lang v (y.eraseIdx i) := by
  rcases hy with hsub | ⟨⟨u, hu, hnot, rfl⟩, hlex⟩
  · exact Or.inl ((List.eraseIdx_sublist y i).trans hsub)
  · have hi' : i < u.length + 1 := by simpa using hi
    have hile : i ≤ u.length := Nat.lt_succ_iff.mp hi'
    rcases hile.lt_or_eq with hil | rfl
    · have herase : (u ++ [true]).eraseIdx i = u.eraseIdx i ++ [true] :=
        List.eraseIdx_append_of_lt_length hil [true]
      rw [herase]
      by_cases hz : (u.eraseIdx i ++ [true]).Sublist v
      · exact Or.inl hz
      · exact Or.inr ⟨boundaryOne_append ((List.eraseIdx_sublist u i).trans hu) hz,
          lex_trans (by
            rw [← herase]
            exact lex_delete_true (u ++ [true]) i hi hbit) hlex⟩
    · have herase : (u ++ [true]).eraseIdx u.length = u := by
        simp [List.eraseIdx_append_of_length_le]
      rw [herase]
      exact Or.inl hu
def subwordFinset (v : Word) : Finset Word := v.sublists.toFinset
def boundaryOneFinset (v : Word) : Finset Word :=
  ((subwordFinset v).image fun u => u ++ [true]).filter fun y => ¬ y.Sublist v
noncomputable def langFinset (v : Word) : Finset Word := by
  classical
  exact subwordFinset v ∪ (boundaryOneFinset v).filter fun y => LexLT y v
theorem mem_subwordFinset {v y : Word} : y ∈ subwordFinset v ↔ y.Sublist v := by
  simp [subwordFinset, List.mem_sublists]
theorem mem_boundaryOneFinset {v y : Word} :
    y ∈ boundaryOneFinset v ↔ BoundaryOne v y := by
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hy, hnot⟩
    rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
    exact ⟨u, mem_subwordFinset.mp hu, hnot, rfl⟩
  · rintro ⟨u, hu, hnot, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨u, mem_subwordFinset.mpr hu, rfl⟩, hnot⟩
theorem mem_langFinset {v y : Word} : y ∈ langFinset v ↔ Lang v y := by
  classical
  simp only [langFinset, Finset.mem_union, Finset.mem_filter, mem_subwordFinset,
    mem_boundaryOneFinset, Lang]
theorem langFinset_delete_closed (v : Word) :
    ∀ y ∈ langFinset v, ∀ i, (hi : i < y.length) → y[i] = true →
      y.eraseIdx i ∈ langFinset v := by
  intro y hy i hi hbit
  exact mem_langFinset.mpr (lang_eraseIdx_true (mem_langFinset.mp hy) i hi hbit)
theorem boundaryOne_ones_le {v y : Word} (hy : BoundaryOne v y)
    (hlex : LexLT y v) : ones y ≤ ones v := by
  rcases hy with ⟨u, hu, hnot, rfl⟩
  induction v generalizing u with
  | nil =>
      have : u = [] := List.sublist_nil.mp hu
      subst u
      simp at hlex
  | cons b v ih =>
      cases u with
      | nil =>
          cases b
          · simp [LexLT] at hlex
          · simp [ones]
      | cons a u =>
          cases a <;> cases b
          · have hu' : u.Sublist v := List.cons_sublist_cons.mp hu
            have hnot' : ¬ (u ++ [true]).Sublist v := by
              simpa using hnot
            have hlex' : LexLT (u ++ [true]) v := by simpa using hlex
            simpa [ones] using ih u hu' hlex' hnot'
          · have husub : (false :: u).Sublist v := by
              rcases List.sublist_cons_iff.mp hu with huv | ⟨r, hbad, _⟩
              · exact huv
              · simp at hbad
            have hcount := husub.count_le true
            simp [ones] at hcount ⊢
            omega
          · simp [LexLT] at hlex
          · have hu' : u.Sublist v := List.cons_sublist_cons.mp hu
            have hnot' : ¬ (u ++ [true]).Sublist v := by
              simpa using hnot
            have hlex' : LexLT (u ++ [true]) v := by simpa using hlex
            have hrec := ih u hu' hlex' hnot'
            simpa [ones] using Nat.add_le_add_right hrec 1
theorem lang_ones_le {v y : Word} (hy : Lang v y) : ones y ≤ ones v := by
  rcases hy with hsub | ⟨hboundary, hlex⟩
  · exact hsub.count_le true
  · exact boundaryOne_ones_le hboundary hlex
theorem langFinset_ones_le {v y : Word} (hy : y ∈ langFinset v) :
    ones y ≤ ones v := lang_ones_le (mem_langFinset.mp hy)
theorem exists_sublist_with_counts (v : Word) (a b : ℕ)
    (ha : a ≤ zeros v) (hb : b ≤ ones v) :
    ∃ u, u.Sublist v ∧ zeros u = a ∧ ones u = b := by
  induction v generalizing a b with
  | nil =>
      have ha0 : a = 0 := by simpa [zeros] using ha
      have hb0 : b = 0 := by simpa [ones] using hb
      subst a
      subst b
      exact ⟨[], List.nil_sublist [], by simp [zeros, ones]⟩
  | cons x v ih =>
      cases x
      · cases a with
        | zero =>
            obtain ⟨u, hu, hzu, hou⟩ := ih 0 b (by simp [zeros]) (by simpa [ones] using hb)
            exact ⟨u, hu.cons false, hzu, hou⟩
        | succ a =>
            have ha' : a ≤ zeros v := by simpa [zeros] using ha
            obtain ⟨u, hu, hzu, hou⟩ := ih a b ha' (by simpa [ones] using hb)
            exact ⟨false :: u, hu.cons₂ false, by simpa [zeros, ones] using hzu,
              by simpa [zeros, ones] using hou⟩
      · cases b with
        | zero =>
            obtain ⟨u, hu, hzu, hou⟩ := ih a 0 (by simpa [zeros] using ha) (by simp [ones])
            exact ⟨u, hu.cons true, hzu, hou⟩
        | succ b =>
            have hb' : b ≤ ones v := by simpa [ones] using hb
            obtain ⟨u, hu, hzu, hou⟩ := ih a b (by simpa [zeros] using ha) hb'
            exact ⟨true :: u, hu.cons₂ true, by simpa [zeros, ones] using hzu,
              by simpa [zeros, ones] using hou⟩
def layer (L : Finset Word) (a b : ℕ) : Finset Word :=
  L.filter fun w => zeros w = a ∧ ones w = b
def truePositions (w : Word) : Finset ℕ :=
  (Finset.range w.length).filter fun i => w[i]? = some true
theorem card_truePositions (w : Word) : (truePositions w).card = ones w := by
  simp only [truePositions, Finset.card_filter]
  induction w with
  | nil => simp [ones]
  | cons b w ih =>
      simp only [List.length_cons]
      rw [Finset.sum_range_succ']
      simp [ones, List.count_cons]
      first
        | exact ih
        | (rw [Finset.card_filter]; simp only [ones] at ih; rw [ih])
        | (simp only [ones] at ih; rw [← ih, Finset.card_filter])
def markedOnes (L : Finset Word) (a b : ℕ) : Finset (Σ _ : Word, ℕ) :=
  (layer L a b).sigma fun w => truePositions w
def insertionSlots (L : Finset Word) (a b : ℕ) : Finset (Σ _ : Word, ℕ) :=
  (layer L a b).sigma fun w => Finset.range (w.length + 1)
theorem count_eraseIdx_true {w : Word} {i : ℕ} (hi : i < w.length)
    (hbit : w[i] = true) :
    zeros (w.eraseIdx i) = zeros w ∧ ones (w.eraseIdx i) = ones w - 1 := by
  have hp := List.getElem_cons_eraseIdx_perm hi
  have hzero := hp.count_eq false
  have hone := hp.count_eq true
  simp [hbit] at hzero hone
  constructor
  · simpa [zeros] using hzero
  · dsimp [ones]
    omega
theorem card_markedOnes (L : Finset Word) (a b : ℕ) :
    (markedOnes L a b).card = b * (layer L a b).card := by
  rw [markedOnes, Finset.card_sigma]
  simp_rw [card_truePositions]
  have h : ∀ w ∈ layer L a b, ones w = b := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2.2
  calc
    ∑ w ∈ layer L a b, ones w = ∑ _w ∈ layer L a b, b := by
      apply Finset.sum_congr rfl
      intro w hw
      exact h w hw
    _ = b * (layer L a b).card := by simp [Nat.mul_comm]
theorem card_insertionSlots (L : Finset Word) (a b : ℕ) :
    (insertionSlots L a b).card = (a + b + 1) * (layer L a b).card := by
  rw [insertionSlots, Finset.card_sigma]
  have hlen : ∀ w ∈ layer L a b, w.length + 1 = a + b + 1 := by
    intro w hw
    have hw' := (Finset.mem_filter.mp hw).2
    rw [← zeros_add_ones w, hw'.1, hw'.2]
  simp_rw [Finset.card_range]
  calc
    ∑ w ∈ layer L a b, (w.length + 1) =
        ∑ _w ∈ layer L a b, (a + b + 1) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hlen w hw
    _ = (a + b + 1) * (layer L a b).card := by simp [Nat.mul_comm]
def markedDelete (p : Σ _ : Word, ℕ) : Σ _ : Word, ℕ :=
  ⟨p.1.eraseIdx p.2, p.2⟩
theorem markedDelete_injective_on (L : Finset Word) (a b : ℕ) :
    Set.InjOn markedDelete (markedOnes L a b : Set (Σ _ : Word, ℕ)) := by
  intro p hp q hq heq
  have hp' := Finset.mem_sigma.mp hp
  have hq' := Finset.mem_sigma.mp hq
  have hipos := Finset.mem_range.mp (Finset.mem_filter.mp hp'.2).1
  have hqpos := Finset.mem_range.mp (Finset.mem_filter.mp hq'.2).1
  have hpbit? := (Finset.mem_filter.mp hp'.2).2
  have hqbit? := (Finset.mem_filter.mp hq'.2).2
  have hpbit : p.1[p.2] = true := by
    exact (List.getElem?_eq_some_iff.mp hpbit?).choose_spec
  have hqbit : q.1[q.2] = true := by
    exact (List.getElem?_eq_some_iff.mp hqbit?).choose_spec
  have hi : p.2 = q.2 := congrArg Sigma.snd heq
  have hl : p.1.eraseIdx p.2 = q.1.eraseIdx q.2 := congrArg Sigma.fst heq
  have hlist : p.1 = q.1 := calc
    p.1 = (p.1.eraseIdx p.2).insertIdx p.2 true := by
      symm
      simpa [hpbit] using List.insertIdx_eraseIdx_getElem hipos
    _ = (q.1.eraseIdx q.2).insertIdx q.2 true := by rw [hl, hi]
    _ = q.1 := by simpa [hqbit] using List.insertIdx_eraseIdx_getElem hqpos
  exact Sigma.ext hlist (heq_of_eq hi)
theorem marked_deletion_inequality
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (a b : ℕ) (hb : 1 ≤ b) :
    b * (layer L a b).card ≤ (a + b) * (layer L a (b - 1)).card := by
  have hmap : Set.MapsTo markedDelete
      (markedOnes L a b : Set (Σ _ : Word, ℕ))
      (insertionSlots L a (b - 1) : Set (Σ _ : Word, ℕ)) := by
    intro p hp
    have hp' := Finset.mem_sigma.mp hp
    have hwlayer := hp'.1
    have hpos := Finset.mem_filter.mp hp'.2
    have hi : p.2 < p.1.length := Finset.mem_range.mp hpos.1
    have hbit : p.1[p.2] = true := by
      exact (List.getElem?_eq_some_iff.mp hpos.2).choose_spec
    have hw := (Finset.mem_filter.mp hwlayer).1
    have hcounts := (Finset.mem_filter.mp hwlayer).2
    have herase := count_eraseIdx_true hi hbit
    have hmem : (⟨p.1.eraseIdx p.2, p.2⟩ : Σ _ : Word, ℕ) ∈
        insertionSlots L a (b - 1) := by
      rw [insertionSlots, Finset.mem_sigma]
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨hclosed p.1 hw p.2 hi hbit,
          by simpa [hcounts.1, hcounts.2] using herase⟩
      · apply Finset.mem_range.mpr
        change p.2 < (p.1.eraseIdx p.2).length + 1
        rw [List.length_eraseIdx_of_lt hi]
        omega
    exact hmem
  have hcard := Finset.card_le_card_of_injOn markedDelete hmap
    (markedDelete_injective_on L a b)
  rw [card_markedOnes, card_insertionSlots] at hcard
  have harith : a + (b - 1) + 1 = a + b := by omega
  simpa [harith] using hcard
theorem diagonal_subdiagonal
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (m : ℕ) (hm : 1 ≤ m) :
    (layer L m m).card ≤ 2 * (layer L m (m - 1)).card := by
  have h := marked_deletion_inequality L hclosed m m hm
  have hmpos : 0 < m := hm
  apply Nat.le_of_mul_le_mul_left (c := m)
  · calc
      m * (layer L m m).card ≤ (m + m) * (layer L m (m - 1)).card := h
      _ = m * (2 * (layer L m (m - 1)).card) := by ring
  · exact hmpos
def jCoeff (L : Finset Word) (a b : ℕ) : ℕ := (layer L a b).card
theorem lex_language_subdiagonal_nonempty (v : Word) (h : ones v < zeros v) :
    1 ≤ jCoeff (langFinset v) (ones v + 1) (ones v) := by
  obtain ⟨u, hu, hzu, hou⟩ := exists_sublist_with_counts v (ones v + 1) (ones v)
    (by omega) (le_refl _)
  rw [jCoeff, Finset.one_le_card]
  exact ⟨u, Finset.mem_filter.mpr ⟨mem_langFinset.mpr (Or.inl hu), hzu, hou⟩⟩
theorem lex_language_high_diagonal_zero (v : Word) :
    jCoeff (langFinset v) (ones v + 1) (ones v + 1) = 0 := by
  rw [jCoeff, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨y, hy⟩
  have hy' := Finset.mem_filter.mp hy
  have hle := langFinset_ones_le hy'.1
  omega
def defectTerm (L : Finset Word) (m : ℕ) : ℚ :=
  (jCoeff L m m : ℚ) / (2 : ℚ) ^ (2 * m + 1) -
    (jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m)
def halfplaneDefect (L : Finset Word) (M : ℕ) : ℚ :=
  1 / 2 + ∑ m ∈ Finset.Icc 1 M, defectTerm L m
theorem defectTerm_nonpos
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (m : ℕ) (hm : 1 ≤ m) : defectTerm L m ≤ 0 := by
  have hnat := diagonal_subdiagonal L hclosed m hm
  have hq : (jCoeff L m m : ℚ) ≤ 2 * (jCoeff L m (m - 1) : ℚ) := by
    exact_mod_cast hnat
  have hpow : (0 : ℚ) < (2 : ℚ) ^ (2 * m + 1) := by positivity
  have hdiv : (jCoeff L m m : ℚ) / (2 : ℚ) ^ (2 * m + 1) ≤
      (2 * (jCoeff L m (m - 1) : ℚ)) / (2 : ℚ) ^ (2 * m + 1) :=
    div_le_div_of_nonneg_right hq hpow.le
  have hid : (2 * (jCoeff L m (m - 1) : ℚ)) / (2 : ℚ) ^ (2 * m + 1) =
      (jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m) := by
    rw [show 2 * m + 1 = (2 * m) + 1 by omega, pow_succ]
    field_simp
    <;> ring
  dsimp [defectTerm]
  linarith
theorem halfplaneDefect_le_half
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (M : ℕ) : halfplaneDefect L M ≤ 1 / 2 := by
  have hsum : (∑ m ∈ Finset.Icc 1 M, defectTerm L m) ≤ 0 := by
    apply Finset.sum_nonpos
    intro m hm
    exact defectTerm_nonpos L hclosed m (Finset.mem_Icc.mp hm).1
  dsimp [halfplaneDefect]
  linarith
theorem defectTerm_le_negative_unit
    (L : Finset Word) (m : ℕ)
    (hdiag : jCoeff L m m = 0)
    (hsub : 1 ≤ jCoeff L m (m - 1)) :
    defectTerm L m ≤ -(1 / (2 : ℚ) ^ (2 * m)) := by
  have hq : (1 : ℚ) ≤ (jCoeff L m (m - 1) : ℚ) := by exact_mod_cast hsub
  have hp : (0 : ℚ) < (2 : ℚ) ^ (2 * m) := by positivity
  have hdiv : (1 : ℚ) / (2 : ℚ) ^ (2 * m) ≤
      (jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m) :=
    div_le_div_of_nonneg_right hq hp.le
  simp only [defectTerm, hdiag, Nat.cast_zero, zero_div, zero_sub]
  linarith
theorem halfplaneDefect_strict_room
    (L : Finset Word)
    (hclosed : ∀ w ∈ L, ∀ i, (hi : i < w.length) → w[i] = true → w.eraseIdx i ∈ L)
    (M m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hM : m₀ ≤ M)
    (hdiag : jCoeff L m₀ m₀ = 0)
    (hsub : 1 ≤ jCoeff L m₀ (m₀ - 1)) :
    halfplaneDefect L M ≤ 1 / 2 - 1 / (2 : ℚ) ^ (2 * m₀) := by
  let S := Finset.Icc 1 M
  let gap : ℚ := 1 / (2 : ℚ) ^ (2 * m₀)
  have hm₀S : m₀ ∈ S := by simp [S, hm₀, hM]
  have hpoint : ∀ m ∈ S, defectTerm L m ≤ if m = m₀ then -gap else 0 := by
    intro m hm
    by_cases heq : m = m₀
    · subst m
      simpa [gap] using defectTerm_le_negative_unit L m₀ hdiag hsub
    · simp only [heq, if_false]
      exact defectTerm_nonpos L hclosed m (Finset.mem_Icc.mp hm).1
  have hsum : (∑ m ∈ S, defectTerm L m) ≤ ∑ m ∈ S, if m = m₀ then -gap else 0 := by
    exact Finset.sum_le_sum fun m hm => hpoint m hm
  have hrhs : (∑ m ∈ S, if m = m₀ then -gap else 0) = -gap := by
    rw [Finset.sum_eq_single m₀]
    · simp
    · intro b hb hbne
      simp [hbne]
    · exact fun hnot => (hnot hm₀S).elim
  rw [hrhs] at hsum
  dsimp [halfplaneDefect]
  change 1 / 2 + (∑ m ∈ S, defectTerm L m) ≤ _
  dsimp [gap] at hsum ⊢
  linarith
def exceptionMass (v : Word) : ℚ :=
  if ones v < zeros v then 1 / (2 : ℚ) ^ (zeros v + ones v + 2) else 0
theorem lex_language_halfplane_with_exception (v : Word) (M : ℕ)
    (hM : ones v + 1 ≤ M) :
    halfplaneDefect (langFinset v) M + exceptionMass v ≤ 1 / 2 := by
  by_cases hzo : ones v < zeros v
  · have hroom := halfplaneDefect_strict_room (langFinset v)
      (langFinset_delete_closed v) M (ones v + 1) (by omega) hM
      (lex_language_high_diagonal_zero v)
      (by simpa using lex_language_subdiagonal_nonempty v hzo)
    have hexp : 2 * ones v + 3 ≤ zeros v + ones v + 2 := by omega
    have hpow : (2 : ℚ) ^ (2 * ones v + 3) ≤
        (2 : ℚ) ^ (zeros v + ones v + 2) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hrecip : 1 / (2 : ℚ) ^ (zeros v + ones v + 2) ≤
        1 / (2 : ℚ) ^ (2 * ones v + 3) :=
      one_div_le_one_div_of_le (by positivity) hpow
    have hhalf : 1 / (2 : ℚ) ^ (2 * ones v + 3) =
        (1 / 2) * (1 / (2 : ℚ) ^ (2 * (ones v + 1))) := by
      rw [show 2 * ones v + 3 = 2 * (ones v + 1) + 1 by omega, pow_succ]
      field_simp
      <;> ring
    rw [exceptionMass, if_pos hzo]
    rw [hhalf] at hrecip
    have hgap : (0 : ℚ) < 1 / (2 : ℚ) ^ (2 * (ones v + 1)) := by positivity
    linarith
  · rw [exceptionMass, if_neg hzo, add_zero]
    exact halfplaneDefect_le_half (langFinset v) (langFinset_delete_closed v) M
theorem lex_language_halfplane_bound (v : Word) (M : ℕ) :
    halfplaneDefect (langFinset v) M ≤ 1 / 2 := by
  exact halfplaneDefect_le_half (langFinset v) (langFinset_delete_closed v) M
end TuDeng.FirstExit
end
section
namespace TuDeng.FirstExit
def Boundary (v : Word) (b : Bool) (y : Word) : Prop :=
  ∃ u, u.Sublist v ∧ ¬ y.Sublist v ∧ y = u ++ [b]
theorem boundary_true_iff {v y : Word} : Boundary v true y ↔ BoundaryOne v y := by
  rfl
theorem sublist_concat_iff (y v : Word) (b : Bool) :
    y.Sublist (v ++ [b]) ↔ y.Sublist v ∨ ∃ u, u.Sublist v ∧ y = u ++ [b] := by
  rw [List.sublist_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, h₁, h₂⟩
    have h₂' : l₂ = [] ∨ l₂ = [b] := by simpa using h₂
    rcases h₂' with rfl | rfl
    · exact Or.inl (by simpa using h₁)
    · exact Or.inr ⟨l₁, h₁, rfl⟩
  · rintro (h | ⟨u, hu, rfl⟩)
    · exact ⟨y, [], by simp, h, List.nil_sublist [b]⟩
    · exact ⟨u, [b], rfl, hu, by simp⟩
theorem append_singleton_injective (b : Bool) :
    Function.Injective (fun y : Word => y ++ [b]) := by
  intro x y h
  exact List.append_cancel_right h
theorem singleton_suffix_eq {u v : Word} {a b : Bool}
    (h : u ++ [a] = v ++ [b]) : a = b := by
  have hlen : u.length = v.length := by
    have := congrArg List.length h
    simp at this
    omega
  have hs := (List.append_inj h hlen).2
  simpa using hs
theorem boundary_concat_same {v y : Word} {b : Bool} :
    Boundary (v ++ [b]) b y ↔
      ∃ x, Boundary v b x ∧ y = x ++ [b] := by
  constructor
  · rintro ⟨u, hu, hnot, rfl⟩
    rcases (sublist_concat_iff u v b).mp hu with huold | ⟨p, hp, rfl⟩
    · exact (hnot ((sublist_concat_iff (u ++ [b]) v b).mpr
        (Or.inr ⟨u, huold, rfl⟩))).elim
    · have hpb : ¬ (p ++ [b]).Sublist v := by
        intro hpb
        exact hnot ((sublist_concat_iff (p ++ [b] ++ [b]) v b).mpr
          (Or.inr ⟨p ++ [b], hpb, rfl⟩))
      exact ⟨p ++ [b], ⟨p, hp, hpb, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨p, hp, hxnot, rfl⟩, rfl⟩
    refine ⟨p ++ [b], (sublist_concat_iff (p ++ [b]) v b).mpr
      (Or.inr ⟨p, hp, rfl⟩), ?_, rfl⟩
    intro hbad
    rcases (sublist_concat_iff (p ++ [b] ++ [b]) v b).mp hbad with hold | ⟨q, hq, heq⟩
    · exact hxnot ((List.sublist_append_left (p ++ [b]) [b]).trans hold)
    · have : p ++ [b] = q := List.append_cancel_right heq
      exact hxnot (this ▸ hq)
theorem boundary_concat_other {v y : Word} {b c : Bool} (hbc : c ≠ b) :
    Boundary (v ++ [b]) c y ↔
      Boundary v c y ∨ ∃ x, Boundary v b x ∧ y = x ++ [c] := by
  constructor
  · rintro ⟨u, hu, hnot, rfl⟩
    by_cases huold : u.Sublist v
    · exact Or.inl ⟨u, huold, fun hy => hnot ((List.sublist_append_of_sublist_left hy)), rfl⟩
    · rcases (sublist_concat_iff u v b).mp hu with _ | ⟨p, hp, rfl⟩
      · contradiction
      · exact Or.inr ⟨p ++ [b], ⟨p, hp, huold, rfl⟩, rfl⟩
  · rintro (⟨u, hu, hnot, rfl⟩ | ⟨x, ⟨p, hp, hxnot, rfl⟩, rfl⟩)
    · refine ⟨u, List.sublist_append_of_sublist_left hu, ?_, rfl⟩
      intro hbad
      rcases (sublist_concat_iff (u ++ [c]) v b).mp hbad with hold | ⟨q, hq, heq⟩
      · exact hnot hold
      · exact hbc (singleton_suffix_eq heq)
    · refine ⟨p ++ [b], (sublist_concat_iff (p ++ [b]) v b).mpr
        (Or.inr ⟨p, hp, rfl⟩), ?_, rfl⟩
      intro hbad
      rcases (sublist_concat_iff (p ++ [b] ++ [c]) v b).mp hbad with hold | ⟨q, hq, heq⟩
      · exact hxnot ((List.sublist_append_left (p ++ [b]) [c]).trans hold)
      · exact hbc (singleton_suffix_eq heq)
theorem lex_boundary_append_target {v x : Word} {b : Bool}
    (hx : Boundary v b x) (c : Bool) :
    LexLT (x ++ [c]) (v ++ [b]) ↔ LexLT x v := by
  rcases hx with ⟨p, hp, hnot, rfl⟩
  induction v generalizing p with
  | nil =>
      have : p = [] := List.sublist_nil.mp hp
      subst p
      simp [LexLT]
  | cons a v ih =>
      cases p with
      | nil =>
          cases a <;> cases b <;> cases c <;> simp_all [LexLT]
      | cons d p =>
          cases d <;> cases a
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [b]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'
          · simp [LexLT]
          · simp [LexLT]
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [b]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'
theorem lex_old_one_against_zero {v x : Word} (hx : Boundary v true x) :
    LexLT x (v ++ [false]) ↔ LexLT x v := by
  rcases hx with ⟨p, hp, hnot, rfl⟩
  induction v generalizing p with
  | nil =>
      have : p = [] := List.sublist_nil.mp hp
      subst p
      simp [LexLT]
  | cons a v ih =>
      cases p with
      | nil => cases a <;> simp_all [LexLT]
      | cons d p =>
          cases d <;> cases a
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [true]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'
          · simp [LexLT]
          · simp [LexLT]
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [true]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'
theorem lex_old_zero_against_one {v x : Word} (hx : Boundary v false x) :
    LexLT x (v ++ [true]) ↔ LexLT x v ∨ x = v ++ [false] := by
  rcases hx with ⟨p, hp, hnot, rfl⟩
  induction v generalizing p with
  | nil =>
      have : p = [] := List.sublist_nil.mp hp
      subst p
      simp [LexLT]
  | cons a v ih =>
      cases p with
      | nil => cases a <;> simp_all [LexLT]
      | cons d p =>
          cases d <;> cases a
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [false]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'
          · simp [LexLT]
          · simp [LexLT]
          · have hp' : p.Sublist v := List.cons_sublist_cons.mp hp
            have hnot' : ¬ (p ++ [false]).Sublist v := by simpa using hnot
            simpa using ih p hp' hnot'
def LexBoundary (v : Word) (b : Bool) (y : Word) : Prop :=
  Boundary v b y ∧ LexLT y v
theorem lexBoundary_concat_same {v y : Word} {b : Bool} :
    LexBoundary (v ++ [b]) b y ↔
      ∃ x, LexBoundary v b x ∧ y = x ++ [b] := by
  rw [LexBoundary, boundary_concat_same]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hlex⟩
    exact ⟨x, ⟨hx, (lex_boundary_append_target hx b).mp hlex⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hlex⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (lex_boundary_append_target hx b).mpr hlex⟩
theorem lexBoundary_one_concat_zero {v y : Word} :
    LexBoundary (v ++ [false]) true y ↔
      LexBoundary v true y ∨
        ∃ x, LexBoundary v false x ∧ y = x ++ [true] := by
  rw [LexBoundary, boundary_concat_other (by decide : true ≠ false)]
  constructor
  · rintro ⟨hold | ⟨x, hx, rfl⟩, hlex⟩
    · exact Or.inl ⟨hold, (lex_old_one_against_zero hold).mp hlex⟩
    · exact Or.inr ⟨x, ⟨hx, (lex_boundary_append_target hx true).mp hlex⟩, rfl⟩
  · rintro (⟨hold, hlex⟩ | ⟨x, ⟨hx, hlex⟩, rfl⟩)
    · exact ⟨Or.inl hold, (lex_old_one_against_zero hold).mpr hlex⟩
    · exact ⟨Or.inr ⟨x, hx, rfl⟩, (lex_boundary_append_target hx true).mpr hlex⟩
theorem lexBoundary_zero_concat_one {v y : Word} :
    LexBoundary (v ++ [true]) false y ↔
      LexBoundary v false y ∨
        (∃ x, LexBoundary v true x ∧ y = x ++ [false]) ∨ y = v ++ [false] := by
  rw [LexBoundary, boundary_concat_other (by decide : false ≠ true)]
  constructor
  · rintro ⟨hold | ⟨x, hx, rfl⟩, hlex⟩
    · rcases (lex_old_zero_against_one hold).mp hlex with hlex | rfl
      · exact Or.inl ⟨hold, hlex⟩
      · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl ⟨x, ⟨hx, (lex_boundary_append_target hx false).mp hlex⟩, rfl⟩)
  · rintro (⟨hold, hlex⟩ | (⟨x, ⟨hx, hlex⟩, rfl⟩ | rfl))
    · exact ⟨Or.inl hold, (lex_old_zero_against_one hold).mpr (Or.inl hlex)⟩
    · exact ⟨Or.inr ⟨x, hx, rfl⟩, (lex_boundary_append_target hx false).mpr hlex⟩
    · have hvb : Boundary v false (v ++ [false]) :=
        ⟨v, List.Sublist.refl v, (by
          intro h
          have hlen := h.length_le
          simp at hlen), rfl⟩
      exact ⟨Or.inl hvb, (lex_old_zero_against_one hvb).mpr (Or.inr rfl)⟩
end TuDeng.FirstExit
end
section
namespace TuDeng.FirstExit
open scoped BigOperators
def boundaryFinset (v : Word) (b : Bool) : Finset Word :=
  ((subwordFinset v).image fun u => u ++ [b]).filter fun y => ¬ y.Sublist v
noncomputable def lexBoundaryFinset (v : Word) (b : Bool) : Finset Word := by
  classical
  exact (boundaryFinset v b).filter fun y => LexLT y v
theorem mem_boundaryFinset {v y : Word} {b : Bool} :
    y ∈ boundaryFinset v b ↔ Boundary v b y := by
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hy, hnot⟩
    rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
    exact ⟨u, mem_subwordFinset.mp hu, hnot, rfl⟩
  · rintro ⟨u, hu, hnot, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨u, mem_subwordFinset.mpr hu, rfl⟩, hnot⟩
theorem mem_lexBoundaryFinset {v y : Word} {b : Bool} :
    y ∈ lexBoundaryFinset v b ↔ LexBoundary v b y := by
  classical
  simp [lexBoundaryFinset, mem_boundaryFinset, LexBoundary]
theorem lexBoundaryFinset_concat_same (v : Word) (b : Bool) :
    lexBoundaryFinset (v ++ [b]) b =
      (lexBoundaryFinset v b).image (fun y => y ++ [b]) := by
  classical
  ext y
  rw [mem_lexBoundaryFinset, lexBoundary_concat_same]
  simp only [Finset.mem_image, mem_lexBoundaryFinset]
  aesop
theorem lexBoundaryFinset_one_concat_zero (v : Word) :
    lexBoundaryFinset (v ++ [false]) true =
      lexBoundaryFinset v true ∪
        (lexBoundaryFinset v false).image (fun y => y ++ [true]) := by
  classical
  ext y
  rw [mem_lexBoundaryFinset, lexBoundary_one_concat_zero]
  simp only [Finset.mem_union, Finset.mem_image, mem_lexBoundaryFinset]
  aesop
theorem lexBoundaryFinset_zero_concat_one (v : Word) :
    lexBoundaryFinset (v ++ [true]) false =
      (lexBoundaryFinset v false ∪
        (lexBoundaryFinset v true).image (fun y => y ++ [false])) ∪
          {v ++ [false]} := by
  classical
  ext y
  rw [mem_lexBoundaryFinset, lexBoundary_zero_concat_one]
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
    mem_lexBoundaryFinset]
  aesop
abbrev BiPoly := MvPolynomial Bool ℤ
noncomputable def X : BiPoly := MvPolynomial.X false
noncomputable def Y : BiPoly := MvPolynomial.X true
noncomputable def wordMonomial (w : Word) : BiPoly := X ^ zeros w * Y ^ ones w
noncomputable def enumerator (S : Finset Word) : BiPoly := ∑ w ∈ S, wordMonomial w
theorem wordMonomial_append_false (w : Word) :
    wordMonomial (w ++ [false]) = X * wordMonomial w := by
  simp [wordMonomial, X, Y, zeros, ones, List.count_append]
  ring
theorem wordMonomial_append_true (w : Word) :
    wordMonomial (w ++ [true]) = Y * wordMonomial w := by
  simp [wordMonomial, X, Y, zeros, ones, List.count_append]
  ring
theorem enumerator_image_append (S : Finset Word) (b : Bool) :
    enumerator (S.image fun w => w ++ [b]) =
      (if b then Y else X) * enumerator S := by
  classical
  have hinj : Set.InjOn (fun w : Word => w ++ [b]) (S : Set Word) :=
    fun _ _ _ _ h => append_singleton_injective b h
  rw [enumerator, Finset.sum_image hinj]
  cases b
  · simp_rw [wordMonomial_append_false]
    simp [enumerator, Finset.mul_sum]
  · simp_rw [wordMonomial_append_true]
    simp [enumerator, Finset.mul_sum]
theorem enumerator_union {S T : Finset Word} (h : Disjoint S T) :
    enumerator (S ∪ T) = enumerator S + enumerator T := by
  simp [enumerator, Finset.sum_union h]
theorem enumerator_singleton (w : Word) : enumerator {w} = wordMonomial w := by
  simp [enumerator]
theorem not_lex_append_self (v : Word) (b : Bool) : ¬ LexLT (v ++ [b]) v := by
  induction v with
  | nil => simp
  | cons a v ih => simpa using ih
theorem disjoint_H_image_U (v : Word) : Disjoint (lexBoundaryFinset v true)
    ((lexBoundaryFinset v false).image fun x => x ++ [true]) := by
  classical
  rw [Finset.disjoint_left]
  intro y hy hyimage
  have hy' := (mem_lexBoundaryFinset.mp hy).1
  rcases hy' with ⟨u, hu, _, huy⟩
  rcases Finset.mem_image.mp hyimage with ⟨x, hx, hxy⟩
  have hx' := (mem_lexBoundaryFinset.mp hx).1
  rcases hx' with ⟨p, hp, hxnot, hpx⟩
  have hux : u = x := by
    apply List.append_cancel_right
    calc
      u ++ [true] = y := huy.symm
      _ = x ++ [true] := hxy.symm
  exact hxnot (hux ▸ hu)
theorem disjoint_U_image_H (v : Word) : Disjoint (lexBoundaryFinset v false)
    ((lexBoundaryFinset v true).image fun x => x ++ [false]) := by
  classical
  rw [Finset.disjoint_left]
  intro y hy hyimage
  have hy' := (mem_lexBoundaryFinset.mp hy).1
  rcases hy' with ⟨u, hu, _, huy⟩
  rcases Finset.mem_image.mp hyimage with ⟨x, hx, hxy⟩
  have hx' := (mem_lexBoundaryFinset.mp hx).1
  rcases hx' with ⟨p, hp, hxnot, hpx⟩
  have hux : u = x := by
    apply List.append_cancel_right
    calc
      u ++ [false] = y := huy.symm
      _ = x ++ [false] := hxy.symm
  exact hxnot (hux ▸ hu)
theorem exceptional_not_mem_U (v : Word) :
    v ++ [false] ∉ lexBoundaryFinset v false := by
  intro h
  exact not_lex_append_self v false (mem_lexBoundaryFinset.mp h).2
theorem exceptional_not_mem_image_H (v : Word) :
    v ++ [false] ∉ (lexBoundaryFinset v true).image (fun x => x ++ [false]) := by
  classical
  intro h
  rcases Finset.mem_image.mp h with ⟨x, hx, heq⟩
  have hxv : x = v := append_singleton_injective false heq
  have hboundary := (mem_lexBoundaryFinset.mp hx).1
  rcases hboundary with ⟨u, hu, hnot, hxu⟩
  exact hnot (hxv ▸ List.Sublist.refl v)
noncomputable def Uenum (v : Word) : BiPoly := enumerator (lexBoundaryFinset v false)
noncomputable def Henum (v : Word) : BiPoly := enumerator (lexBoundaryFinset v true)
theorem Uenum_concat_zero (v : Word) : Uenum (v ++ [false]) = X * Uenum v := by
  rw [Uenum, lexBoundaryFinset_concat_same, enumerator_image_append]
  simp [Uenum]
theorem Henum_concat_one (v : Word) : Henum (v ++ [true]) = Y * Henum v := by
  rw [Henum, lexBoundaryFinset_concat_same, enumerator_image_append]
  simp [Henum]
theorem Henum_concat_zero (v : Word) :
    Henum (v ++ [false]) = Henum v + Y * Uenum v := by
  rw [Henum, lexBoundaryFinset_one_concat_zero,
    enumerator_union (disjoint_H_image_U v), enumerator_image_append]
  simp [Henum, Uenum]
theorem Uenum_concat_one (v : Word) :
    Uenum (v ++ [true]) = Uenum v + X * Henum v + wordMonomial (v ++ [false]) := by
  have hdis₁ := disjoint_U_image_H v
  have hdis₂ : Disjoint
      (lexBoundaryFinset v false ∪
        (lexBoundaryFinset v true).image (fun x => x ++ [false])) {v ++ [false]} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_union]
    exact not_or_intro (exceptional_not_mem_U v) (exceptional_not_mem_image_H v)
  rw [Uenum, lexBoundaryFinset_zero_concat_one, enumerator_union hdis₂,
    enumerator_union hdis₁, enumerator_image_append, enumerator_singleton]
  simp [Uenum, Henum]
theorem boundaryFinset_concat_same (v : Word) (b : Bool) :
    boundaryFinset (v ++ [b]) b =
      (boundaryFinset v b).image (fun y => y ++ [b]) := by
  classical
  ext y
  rw [mem_boundaryFinset, boundary_concat_same]
  simp only [Finset.mem_image, mem_boundaryFinset]
  aesop
theorem boundaryFinset_concat_other (v : Word) (b c : Bool) (hbc : c ≠ b) :
    boundaryFinset (v ++ [b]) c =
      boundaryFinset v c ∪
        (boundaryFinset v b).image (fun y => y ++ [c]) := by
  classical
  ext y
  rw [mem_boundaryFinset, boundary_concat_other hbc]
  simp only [Finset.mem_union, Finset.mem_image, mem_boundaryFinset]
  aesop
theorem disjoint_boundary_image (v : Word) (b c : Bool) :
    Disjoint (boundaryFinset v c)
      ((boundaryFinset v b).image fun x => x ++ [c]) := by
  classical
  rw [Finset.disjoint_left]
  intro y hy hyimage
  rcases (mem_boundaryFinset.mp hy) with ⟨u, hu, _, huy⟩
  rcases Finset.mem_image.mp hyimage with ⟨x, hx, hxy⟩
  rcases (mem_boundaryFinset.mp hx) with ⟨p, hp, hxnot, hpx⟩
  have hux : u = x := by
    apply List.append_cancel_right
    calc
      u ++ [c] = y := huy.symm
      _ = x ++ [c] := hxy.symm
  exact hxnot (hux ▸ hu)
noncomputable def Benum (v : Word) (b : Bool) : BiPoly :=
  enumerator (boundaryFinset v b)
noncomputable def Ienum (v : Word) : BiPoly := enumerator (subwordFinset v)
theorem Benum_concat_same (v : Word) (b : Bool) :
    Benum (v ++ [b]) b = (if b then Y else X) * Benum v b := by
  rw [Benum, boundaryFinset_concat_same, enumerator_image_append]
  simp [Benum]
theorem Benum_concat_other (v : Word) (b c : Bool) (hbc : c ≠ b) :
    Benum (v ++ [b]) c = Benum v c + (if c then Y else X) * Benum v b := by
  rw [Benum, boundaryFinset_concat_other v b c hbc,
    enumerator_union (disjoint_boundary_image v b c), enumerator_image_append]
  simp [Benum]
theorem Benum_concat_zero_zero (v : Word) :
    Benum (v ++ [false]) false = X * Benum v false := by
  simpa using Benum_concat_same v false
theorem Benum_concat_zero_one (v : Word) :
    Benum (v ++ [false]) true = Benum v true + Y * Benum v false := by
  simpa using Benum_concat_other v false true (by decide)
theorem Benum_concat_one_zero (v : Word) :
    Benum (v ++ [true]) false = Benum v false + X * Benum v true := by
  simpa using Benum_concat_other v true false (by decide)
theorem Benum_concat_one_one (v : Word) :
    Benum (v ++ [true]) true = Y * Benum v true := by
  simpa using Benum_concat_same v true
theorem subwordFinset_concat (v : Word) (b : Bool) :
    subwordFinset (v ++ [b]) = subwordFinset v ∪ boundaryFinset v b := by
  classical
  ext y
  rw [mem_subwordFinset, sublist_concat_iff]
  simp only [Finset.mem_union, mem_subwordFinset, mem_boundaryFinset]
  constructor
  · rintro (hold | ⟨u, hu, rfl⟩)
    · exact Or.inl hold
    · by_cases hnew : (u ++ [b]).Sublist v
      · exact Or.inl hnew
      · exact Or.inr ⟨u, hu, hnew, rfl⟩
  · rintro (hold | ⟨u, hu, _, rfl⟩)
    · exact Or.inl hold
    · exact Or.inr ⟨u, hu, rfl⟩
theorem disjoint_subword_boundary (v : Word) (b : Bool) :
    Disjoint (subwordFinset v) (boundaryFinset v b) := by
  rw [Finset.disjoint_left]
  intro y hy hb
  rcases mem_boundaryFinset.mp hb with ⟨u, _, hnot, rfl⟩
  exact hnot (mem_subwordFinset.mp hy)
theorem Ienum_concat (v : Word) (b : Bool) :
    Ienum (v ++ [b]) = Ienum v + Benum v b := by
  rw [Ienum, subwordFinset_concat,
    enumerator_union (disjoint_subword_boundary v b)]
  rfl
noncomputable def Lambda : BiPoly := X + Y - 1
theorem boundaryFinset_nil (b : Bool) : boundaryFinset [] b = {[b]} := by
  ext y
  simp only [mem_boundaryFinset, Boundary, List.sublist_nil, Finset.mem_singleton]
  constructor
  · rintro ⟨u, rfl, hnot, rfl⟩
    exact rfl
  · rintro rfl
    exact ⟨[], rfl, by simp, rfl⟩
theorem Benum_nil (b : Bool) : Benum [] b = if b then Y else X := by
  cases b <;>
    simp [Benum, boundaryFinset_nil, enumerator_singleton, wordMonomial,
      X, Y, zeros, ones]
theorem lexBoundaryFinset_nil (b : Bool) : lexBoundaryFinset [] b = ∅ := by
  ext y
  rw [mem_lexBoundaryFinset]
  constructor
  · rintro ⟨_, hlex⟩
    cases y <;> simp at hlex
  · intro h
    simp at h
theorem Uenum_nil : Uenum [] = 0 := by simp [Uenum, lexBoundaryFinset_nil, enumerator]
theorem Henum_nil : Henum [] = 0 := by simp [Henum, lexBoundaryFinset_nil, enumerator]
theorem boundary_tree_identity (v : Word) :
    Benum v false + Benum v true = 1 + Lambda * Ienum v := by
  induction v using List.reverseRecOn with
  | nil =>
      rw [Benum_nil, Benum_nil]
      rw [show Ienum [] = 1 by
        simp [Ienum, subwordFinset, enumerator, wordMonomial, X, Y, zeros, ones]]
      dsimp [Lambda]
      ring
  | append_singleton v b ih =>
      cases b
      · rw [Benum_concat_zero_zero, Benum_concat_zero_one,
          Ienum_concat]
        calc
          X * Benum v false + (Benum v true + Y * Benum v false) =
              (Benum v false + Benum v true) + Lambda * Benum v false := by
                dsimp [Lambda]
                ring
          _ = (1 + Lambda * Ienum v) + Lambda * Benum v false := by rw [ih]
          _ = 1 + Lambda * (Ienum v + Benum v false) := by ring
      · rw [Benum_concat_one_zero, Benum_concat_one_one,
          Ienum_concat]
        calc
          Benum v false + X * Benum v true + Y * Benum v true =
              (Benum v false + Benum v true) + Lambda * Benum v true := by
                dsimp [Lambda]
                ring
          _ = (1 + Lambda * Ienum v) + Lambda * Benum v true := by rw [ih]
          _ = 1 + Lambda * (Ienum v + Benum v true) := by ring
noncomputable def dMonomial (v : Word) : BiPoly := wordMonomial (v ++ [false])
noncomputable def sMonomial (v : Word) : BiPoly := Y * dMonomial v
theorem dMonomial_concat_zero (v : Word) :
    dMonomial (v ++ [false]) = X * dMonomial v := by
  change wordMonomial ((v ++ [false]) ++ [false]) = X * wordMonomial (v ++ [false])
  exact wordMonomial_append_false (v ++ [false])
theorem dMonomial_concat_one (v : Word) :
    dMonomial (v ++ [true]) = Y * dMonomial v := by
  change wordMonomial ((v ++ [true]) ++ [false]) = Y * wordMonomial (v ++ [false])
  rw [wordMonomial_append_false, wordMonomial_append_true,
    wordMonomial_append_false]
  ring
theorem sMonomial_eq_Yd (v : Word) : sMonomial v = Y * dMonomial v := rfl
theorem positive_prefix_lift (v : Word) :
    (Benum (false :: v) false - Benum v false =
        -sMonomial v + Lambda * (Uenum v + dMonomial v)) ∧
    (Benum (false :: v) true - Benum v true =
        sMonomial v + Lambda * Henum v) := by
  induction v using List.reverseRecOn with
  | nil =>
      constructor
      · rw [show false :: [] = [] ++ [false] by rfl,
          Benum_concat_zero_zero, Benum_nil, Uenum_nil]
        simp [sMonomial, dMonomial, wordMonomial, X, Y, zeros, ones, Lambda]
        ring
      · rw [show false :: [] = [] ++ [false] by rfl,
          Benum_concat_zero_one, Benum_nil, Henum_nil]
        simp [Benum_nil, sMonomial, dMonomial, wordMonomial, X, Y, zeros, ones,
          Lambda]
  | append_singleton v b ih =>
      rcases ih with ⟨ih₀, ih₁⟩
      cases b
      · rw [show false :: (v ++ [false]) = (false :: v) ++ [false] by simp]
        constructor
        · rw [Benum_concat_zero_zero, Benum_concat_zero_zero,
            Uenum_concat_zero, dMonomial_concat_zero]
          calc
            X * Benum (false :: v) false - X * Benum v false =
                X * (Benum (false :: v) false - Benum v false) := by ring
            _ = X * (-sMonomial v + Lambda * (Uenum v + dMonomial v)) := by rw [ih₀]
            _ = -sMonomial (v ++ [false]) +
                Lambda * (X * Uenum v + X * dMonomial v) := by
                  rw [sMonomial_eq_Yd, sMonomial_eq_Yd, dMonomial_concat_zero]
                  ring
        · rw [Benum_concat_zero_one, Benum_concat_zero_one,
            Henum_concat_zero]
          calc
            (Benum (false :: v) true + Y * Benum (false :: v) false) -
                (Benum v true + Y * Benum v false) =
                (Benum (false :: v) true - Benum v true) +
                  Y * (Benum (false :: v) false - Benum v false) := by ring
            _ = (sMonomial v + Lambda * Henum v) +
                Y * (-sMonomial v + Lambda * (Uenum v + dMonomial v)) := by
                  rw [ih₀, ih₁]
            _ = sMonomial (v ++ [false]) +
                Lambda * (Henum v + Y * Uenum v) := by
                  rw [sMonomial_eq_Yd, sMonomial_eq_Yd, dMonomial_concat_zero]
                  dsimp [Lambda]
                  ring
      · rw [show false :: (v ++ [true]) = (false :: v) ++ [true] by simp]
        constructor
        · rw [Benum_concat_one_zero, Benum_concat_one_zero,
            Uenum_concat_one, dMonomial_concat_one]
          calc
            (Benum (false :: v) false + X * Benum (false :: v) true) -
                (Benum v false + X * Benum v true) =
                (Benum (false :: v) false - Benum v false) +
                  X * (Benum (false :: v) true - Benum v true) := by ring
            _ = (-sMonomial v + Lambda * (Uenum v + dMonomial v)) +
                X * (sMonomial v + Lambda * Henum v) := by rw [ih₀, ih₁]
            _ = -sMonomial (v ++ [true]) +
                Lambda * (Uenum v + X * Henum v + dMonomial v +
                  Y * dMonomial v) := by
                  rw [sMonomial_eq_Yd, sMonomial_eq_Yd, dMonomial_concat_one]
                  dsimp [Lambda]
                  ring
        · rw [Benum_concat_one_one, Benum_concat_one_one,
            Henum_concat_one]
          calc
            Y * Benum (false :: v) true - Y * Benum v true =
                Y * (Benum (false :: v) true - Benum v true) := by ring
            _ = Y * (sMonomial v + Lambda * Henum v) := by rw [ih₁]
            _ = sMonomial (v ++ [true]) + Lambda * (Y * Henum v) := by
                  rw [sMonomial_eq_Yd, sMonomial_eq_Yd, dMonomial_concat_one]
                  ring
noncomputable def Jenum (v : Word) : BiPoly := Ienum v + Henum v
noncomputable def Cenum (v : Word) : BiPoly :=
  Benum (false :: v) true + Benum v false
theorem cross_boundary_identity (v : Word) :
    Cenum v = 1 + Lambda * Jenum v + sMonomial v := by
  have hlift := (positive_prefix_lift v).2
  calc
    Cenum v = (Benum v false + Benum v true) +
        (Benum (false :: v) true - Benum v true) := by
          dsimp [Cenum]
          ring
    _ = (1 + Lambda * Ienum v) +
        (sMonomial v + Lambda * Henum v) := by
          rw [boundary_tree_identity, hlift]
    _ = 1 + Lambda * Jenum v + sMonomial v := by
          dsimp [Jenum]
          ring
theorem langFinset_eq (v : Word) :
    langFinset v = subwordFinset v ∪ lexBoundaryFinset v true := by
  classical
  ext y
  rw [mem_langFinset]
  simp only [Finset.mem_union, mem_subwordFinset, mem_lexBoundaryFinset,
    Lang, LexBoundary, boundary_true_iff]
theorem disjoint_subword_lexBoundary (v : Word) :
    Disjoint (subwordFinset v) (lexBoundaryFinset v true) := by
  rw [Finset.disjoint_left]
  intro y hy hb
  rcases (mem_lexBoundaryFinset.mp hb).1 with ⟨u, _, hnot, rfl⟩
  exact hnot (mem_subwordFinset.mp hy)
theorem enumerator_langFinset (v : Word) :
    enumerator (langFinset v) = Jenum v := by
  rw [langFinset_eq, enumerator_union (disjoint_subword_lexBoundary v)]
  rfl
end TuDeng.FirstExit
end
section
namespace TuDeng.FirstExit
open scoped BigOperators
noncomputable def phiNeg (p : BiPoly) : ℚ :=
  Finsupp.sum (AddMonoidAlgebra.coeff p) fun e c =>
    if e false > e true then (c : ℚ) / (2 : ℚ) ^ (e false + e true) else 0
theorem phiNeg_add (p q : BiPoly) : phiNeg (p + q) = phiNeg p + phiNeg q := by
  unfold phiNeg
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index
  · intro e he
    simp
  · intro e he a b
    by_cases h : e false > e true
    · simp [phiNeg, h]
      push_cast
      ring
    · simp [phiNeg, h]
theorem phiNeg_zero : phiNeg (0 : BiPoly) = 0 := by
  exact Finsupp.sum_zero_index
theorem phiNeg_neg (p : BiPoly) : phiNeg (-p) = -phiNeg p := by
  have h := phiNeg_add p (-p)
  rw [add_neg_cancel, phiNeg_zero] at h
  linarith
theorem phiNeg_sub (p q : BiPoly) : phiNeg (p - q) = phiNeg p - phiNeg q := by
  rw [sub_eq_add_neg, phiNeg_add, phiNeg_neg]
  ring
theorem phiNeg_monomial (e : Bool →₀ ℕ) (c : ℤ) :
    phiNeg ((MvPolynomial.monomial e) c) =
      if e false > e true then (c : ℚ) / (2 : ℚ) ^ (e false + e true) else 0 := by
  unfold phiNeg
  have hc : AddMonoidAlgebra.coeff ((MvPolynomial.monomial e) c) = Finsupp.single e c := rfl
  rw [hc, Finsupp.sum_single_index]
  simp
theorem wordMonomial_eq_monomial (w : Word) :
    wordMonomial w =
      (MvPolynomial.monomial
        (Finsupp.single false (zeros w) + Finsupp.single true (ones w))) 1 := by
  rw [wordMonomial, X, Y, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
  simp
theorem phiNeg_wordMonomial (w : Word) :
    phiNeg (wordMonomial w) =
      if ones w < zeros w then 1 / (2 : ℚ) ^ (zeros w + ones w) else 0 := by
  rw [wordMonomial_eq_monomial, phiNeg_monomial]
  simp [Finsupp.single_apply]
theorem phiNeg_finset_sum {A : Type*} (S : Finset A) (f : A → BiPoly) :
    phiNeg (∑ x ∈ S, f x) = ∑ x ∈ S, phiNeg (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [phiNeg_zero]
  | @insert x S hx ih => simp [hx, phiNeg_add, ih]
theorem phiNeg_enumerator (S : Finset Word) :
    phiNeg (enumerator S) =
      ∑ w ∈ S, if ones w < zeros w then
        1 / (2 : ℚ) ^ (zeros w + ones w) else 0 := by
  rw [enumerator, phiNeg_finset_sum]
  simp_rw [phiNeg_wordMonomial]
@[simp] theorem zeros_append_false (w : Word) : zeros (w ++ [false]) = zeros w + 1 := by
  simp [zeros, List.count_append]
@[simp] theorem ones_append_false (w : Word) : ones (w ++ [false]) = ones w := by
  simp [ones, List.count_append]
@[simp] theorem zeros_append_true (w : Word) : zeros (w ++ [true]) = zeros w := by
  simp [zeros, List.count_append]
@[simp] theorem ones_append_true (w : Word) : ones (w ++ [true]) = ones w + 1 := by
  simp [ones, List.count_append]
theorem phiNeg_Lambda_wordMonomial (w : Word) :
    phiNeg (Lambda * wordMonomial w) =
      if zeros w = ones w then 1 / (2 : ℚ) ^ (2 * zeros w + 1)
      else if zeros w = ones w + 1 then -(1 / (2 : ℚ) ^ (2 * zeros w))
      else 0 := by
  have hpoly : Lambda * wordMonomial w =
      wordMonomial (w ++ [false]) + wordMonomial (w ++ [true]) - wordMonomial w := by
    rw [wordMonomial_append_false, wordMonomial_append_true]
    dsimp [Lambda]
    ring
  rw [hpoly, phiNeg_sub, phiNeg_add, phiNeg_wordMonomial,
    phiNeg_wordMonomial, phiNeg_wordMonomial]
  rw [zeros_append_false, ones_append_false, zeros_append_true, ones_append_true]
  by_cases hd : zeros w = ones w
  · rw [if_pos hd]
    simp only [if_pos (by omega : ones w < zeros w + 1),
      if_neg (by omega : ¬ ones w + 1 < zeros w),
      if_neg (by omega : ¬ ones w < zeros w)]
    rw [show zeros w + 1 + ones w = 2 * zeros w + 1 by omega]
    ring
  · rw [if_neg hd]
    by_cases hs : zeros w = ones w + 1
    · rw [if_pos hs]
      simp only [if_pos (by omega : ones w < zeros w + 1),
        if_neg (by omega : ¬ ones w + 1 < zeros w),
        if_pos (by omega : ones w < zeros w)]
      rw [show zeros w + 1 + ones w = 2 * zeros w by omega,
        show 2 * zeros w = (zeros w + ones w) + 1 by omega, pow_succ]
      field_simp
      ring
    · rw [if_neg hs]
      by_cases hfar : ones w + 2 ≤ zeros w
      · simp only [if_pos (by omega : ones w < zeros w + 1),
          if_pos (by omega : ones w + 1 < zeros w),
          if_pos (by omega : ones w < zeros w)]
        rw [show zeros w + 1 + ones w = (zeros w + ones w) + 1 by omega,
          show zeros w + (ones w + 1) = (zeros w + ones w) + 1 by omega,
          pow_succ]
        field_simp
        ring
      · have hle : zeros w ≤ ones w := by omega
        simp only [if_neg (by omega : ¬ ones w < zeros w + 1),
          if_neg (by omega : ¬ ones w + 1 < zeros w),
          if_neg (by omega : ¬ ones w < zeros w)]
        ring
theorem phiNeg_Lambda_enumerator (L : Finset Word) :
    phiNeg (Lambda * enumerator L) =
      ∑ w ∈ L,
        if zeros w = ones w then 1 / (2 : ℚ) ^ (2 * zeros w + 1)
        else if zeros w = ones w + 1 then -(1 / (2 : ℚ) ^ (2 * zeros w))
        else 0 := by
  rw [enumerator, Finset.mul_sum, phiNeg_finset_sum]
  simp_rw [phiNeg_Lambda_wordMonomial]
private theorem diagonal_filter_eq_layer (L : Finset Word) (m : ℕ) :
    ((L.filter fun w => zeros w = ones w).filter fun w => zeros w = m) =
      layer L m m := by
  ext w
  simp [layer]
  aesop
private theorem subdiagonal_filter_eq_layer (L : Finset Word) (m : ℕ) (hm : 1 ≤ m) :
    ((L.filter fun w => zeros w = ones w + 1).filter fun w => zeros w = m) =
      layer L m (m - 1) := by
  ext w
  simp only [Finset.mem_filter, layer]
  constructor
  · rintro ⟨⟨hw, hsub⟩, hz⟩
    exact ⟨hw, hz, by omega⟩
  · rintro ⟨hw, hz, ho⟩
    exact ⟨⟨hw, by omega⟩, hz⟩
theorem diagonal_sum_eq (L : Finset Word) (M : ℕ)
    (hbound : ∀ w ∈ L, zeros w = ones w → zeros w ≤ M) :
    (∑ w ∈ L, if zeros w = ones w then
        1 / (2 : ℚ) ^ (2 * zeros w + 1) else 0) =
      ∑ m ∈ Finset.Icc 0 M,
        (jCoeff L m m : ℚ) / (2 : ℚ) ^ (2 * m + 1) := by
  classical
  rw [← Finset.sum_filter]
  have hmap : ∀ w ∈ L.filter (fun w => zeros w = ones w),
      zeros w ∈ Finset.Icc 0 M := by
    intro w hw
    simp only [Finset.mem_filter] at hw
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hbound w hw.1 hw.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun w => 1 / (2 : ℚ) ^ (2 * zeros w + 1))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [diagonal_filter_eq_layer]
  calc
    (∑ w ∈ layer L m m, 1 / (2 : ℚ) ^ (2 * zeros w + 1)) =
        ∑ _w ∈ layer L m m, 1 / (2 : ℚ) ^ (2 * m + 1) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [(Finset.mem_filter.mp hw).2.1]
    _ = (jCoeff L m m : ℚ) / (2 : ℚ) ^ (2 * m + 1) := by
          simp [jCoeff, div_eq_mul_inv]
theorem subdiagonal_sum_eq (L : Finset Word) (M : ℕ)
    (hbound : ∀ w ∈ L, zeros w = ones w + 1 → zeros w ≤ M) :
    (∑ w ∈ L, if zeros w = ones w + 1 then
        -(1 / (2 : ℚ) ^ (2 * zeros w)) else 0) =
      ∑ m ∈ Finset.Icc 1 M,
        -((jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m)) := by
  classical
  rw [← Finset.sum_filter]
  have hmap : ∀ w ∈ L.filter (fun w => zeros w = ones w + 1),
      zeros w ∈ Finset.Icc 1 M := by
    intro w hw
    simp only [Finset.mem_filter] at hw
    exact Finset.mem_Icc.mpr ⟨(by omega), hbound w hw.1 hw.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun w => -(1 / (2 : ℚ) ^ (2 * zeros w)))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [subdiagonal_filter_eq_layer L m (Finset.mem_Icc.mp hm).1]
  calc
    (∑ w ∈ layer L m (m - 1), -(1 / (2 : ℚ) ^ (2 * zeros w))) =
        ∑ _w ∈ layer L m (m - 1), -(1 / (2 : ℚ) ^ (2 * m)) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [(Finset.mem_filter.mp hw).2.1]
    _ = -((jCoeff L m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m)) := by
          simp [jCoeff, div_eq_mul_inv]
private theorem lambda_contribution_split (L : Finset Word) :
    (∑ w ∈ L,
      if zeros w = ones w then 1 / (2 : ℚ) ^ (2 * zeros w + 1)
      else if zeros w = ones w + 1 then -(1 / (2 : ℚ) ^ (2 * zeros w))
      else 0) =
    (∑ w ∈ L, if zeros w = ones w then
      1 / (2 : ℚ) ^ (2 * zeros w + 1) else 0) +
    (∑ w ∈ L, if zeros w = ones w + 1 then
      -(1 / (2 : ℚ) ^ (2 * zeros w)) else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hd : zeros w = ones w
  · have hs : ¬ zeros w = ones w + 1 := by omega
    simp [hd, hs]
  · by_cases hs : zeros w = ones w + 1
    · simp [hd, hs]
    · simp [hd, hs]
theorem jCoeff_lang_zero_zero (v : Word) : jCoeff (langFinset v) 0 0 = 1 := by
  rw [jCoeff]
  have hlayer : layer (langFinset v) 0 0 = {[]} := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨_, hz, ho⟩
      have hlen : w.length = 0 := by
        have := zeros_add_ones w
        omega
      have hw_nil : w = [] := List.length_eq_zero_iff.mp hlen
      simpa [hw_nil]
    · intro hw
      have hw_nil : w = [] := by simpa using hw
      subst w
      exact Finset.mem_filter.mpr ⟨mem_langFinset.mpr (Or.inl (List.nil_sublist v)),
        by simp [zeros, ones]⟩
  rw [hlayer]
  simp
private theorem Icc_zero_split (M : ℕ) :
    Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
  ext m
  simp
  omega
theorem phiNeg_Lambda_Jenum (v : Word) :
    phiNeg (Lambda * Jenum v) =
      halfplaneDefect (langFinset v) (ones v + 1) := by
  rw [← enumerator_langFinset, phiNeg_Lambda_enumerator,
    lambda_contribution_split]
  have hdiag := diagonal_sum_eq (langFinset v) (ones v + 1) (by
    intro w hw heq
    have hle := langFinset_ones_le hw
    omega)
  have hsub := subdiagonal_sum_eq (langFinset v) (ones v + 1) (by
    intro w hw heq
    have hle := langFinset_ones_le hw
    omega)
  rw [hdiag, hsub, Icc_zero_split]
  have hzero : 0 ∉ Finset.Icc 1 (ones v + 1) := by simp
  rw [Finset.sum_insert hzero, jCoeff_lang_zero_zero]
  norm_num only [Nat.cast_one, Nat.reduceMul, zero_add, pow_one, one_div]
  have hcombine :
      (∑ m ∈ Finset.Icc 1 (ones v + 1),
          (jCoeff (langFinset v) m m : ℚ) / (2 : ℚ) ^ (2 * m + 1)) +
      (∑ m ∈ Finset.Icc 1 (ones v + 1),
          -((jCoeff (langFinset v) m (m - 1) : ℚ) / (2 : ℚ) ^ (2 * m))) =
      ∑ m ∈ Finset.Icc 1 (ones v + 1), defectTerm (langFinset v) m := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [defectTerm]
    ring
  rw [add_assoc, hcombine]
  rfl
theorem phiNeg_one : phiNeg (1 : BiPoly) = 0 := by
  rw [show (1 : BiPoly) = (MvPolynomial.monomial 0) 1 by simp,
    phiNeg_monomial]
  simp
theorem sMonomial_eq_wordMonomial (v : Word) :
    sMonomial v = wordMonomial ((v ++ [false]) ++ [true]) := by
  rw [wordMonomial_append_true]
  rfl
theorem phiNeg_sMonomial (v : Word) : phiNeg (sMonomial v) = exceptionMass v := by
  rw [sMonomial_eq_wordMonomial, phiNeg_wordMonomial]
  simp only [zeros_append_true, ones_append_true, zeros_append_false, ones_append_false]
  dsimp [exceptionMass]
  by_cases h : ones v < zeros v
  · rw [if_pos h, if_pos (by omega)]
    congr 2
    omega
  · rw [if_neg h, if_neg (by omega)]
theorem phiNeg_Cenum_formula (v : Word) :
    phiNeg (Cenum v) =
      halfplaneDefect (langFinset v) (ones v + 1) + exceptionMass v := by
  rw [cross_boundary_identity, phiNeg_add, phiNeg_add, phiNeg_one,
    phiNeg_Lambda_Jenum, phiNeg_sMonomial, zero_add]
theorem cross_boundary_halfplane_bound (v : Word) :
    phiNeg (Cenum v) ≤ 1 / 2 := by
  rw [phiNeg_Cenum_formula]
  exact lex_language_halfplane_with_exception v (ones v + 1) (le_refl _)
end TuDeng.FirstExit
end
section
namespace TuDeng.FirstExit
open scoped BigOperators
def ValidCode : Word → Bool → Bool → Word → Prop
  | [], c, cf, y => y = [] ∧ c = cf
  | t :: q, c, cf, y =>
      if c = t then ValidCode q c cf y
      else match y with
        | [] => False
        | x :: xs => ValidCode q (!x) cf xs
noncomputable instance validCodeDecidable (q : Word) (c cf : Bool) (y : Word) :
    Decidable (ValidCode q c cf y) := Classical.propDecidable _
def codeMultiplicity : Word → Bool → Bool → Word → ℕ
  | [], c, cf, y => if y = [] ∧ c = cf then 1 else 0
  | t :: q, c, cf, y =>
      if c = t then 2 * codeMultiplicity q c cf y
      else match y with
        | [] => 0
        | x :: xs => codeMultiplicity q (!x) cf xs
theorem validCode_length_le {q y : Word} {c cf : Bool}
    (h : ValidCode q c cf y) : y.length ≤ q.length := by
  induction q generalizing c y with
  | nil => simpa [h.1]
  | cons t q ih =>
      simp only [ValidCode] at h
      split at h
      · exact Nat.le.step (ih h)
      · cases y with
        | nil => contradiction
        | cons x xs =>
            simp only [List.length_cons, Nat.succ_le_succ_iff]
            exact ih h
theorem codeMultiplicity_of_valid {q y : Word} {c cf : Bool}
    (h : ValidCode q c cf y) :
    codeMultiplicity q c cf y = 2 ^ (q.length - y.length) := by
  induction q generalizing c y with
  | nil =>
      rcases h with ⟨rfl, rfl⟩
      simp [codeMultiplicity]
  | cons t q ih =>
      by_cases hct : c = t
      · have htail : ValidCode q c cf y := by simpa [ValidCode, hct] using h
        have hlen := validCode_length_le htail
        cases y with
        | nil =>
            rw [codeMultiplicity, if_pos hct, ih htail]
            simp only [List.length_nil, List.length_cons, Nat.sub_zero]
            rw [pow_succ]
            ring
        | cons x xs =>
            rw [codeMultiplicity, if_pos hct, ih htail]
            have hlen' : xs.length + 1 ≤ q.length := by simpa using hlen
            rw [show (t :: q).length - (x :: xs).length =
                (q.length - (x :: xs).length) + 1 by
              simp only [List.length_cons]
              omega, pow_succ]
            ring
      · have hactive := h
        simp only [ValidCode, hct, if_false] at hactive
        cases y with
        | nil => contradiction
        | cons x xs =>
            change (if c = t then 2 * codeMultiplicity q c cf (x :: xs)
              else codeMultiplicity q (!x) cf xs) = _
            rw [if_neg hct, ih hactive]
            simp only [List.length_cons, Nat.succ_sub_succ_eq_sub]
theorem codeMultiplicity_of_not_valid {q y : Word} {c cf : Bool}
    (h : ¬ ValidCode q c cf y) : codeMultiplicity q c cf y = 0 := by
  induction q generalizing c y with
  | nil =>
      simp only [ValidCode] at h
      simp [codeMultiplicity, h]
  | cons t q ih =>
      by_cases hct : c = t
      · have htail : ¬ ValidCode q c cf y := by simpa [ValidCode, hct] using h
        cases y with
        | nil =>
            rw [codeMultiplicity, if_pos hct, ih htail]
        | cons x xs =>
            rw [codeMultiplicity, if_pos hct, ih htail]
      · cases y with
        | nil =>
            change (if c = t then 2 * codeMultiplicity q c cf [] else 0) = 0
            rw [if_neg hct]
        | cons x xs =>
            change (if c = t then 2 * codeMultiplicity q c cf (x :: xs)
              else codeMultiplicity q (!x) cf xs) = 0
            rw [if_neg hct]
            apply ih
            simpa [ValidCode, hct] using h
private theorem boundary_cons_ne {q xs : Word} {t x b : Bool} (hxt : x ≠ t) :
    Boundary (t :: q) b (x :: xs) ↔ Boundary q b (x :: xs) := by
  constructor
  · rintro ⟨u, hu, hnot, heq⟩
    have huq : u.Sublist q := by
      cases u with
      | nil => exact List.nil_sublist q
      | cons d ds =>
          have hdx : d = x := by simpa using congrArg List.head? heq.symm
          subst d
          simpa [List.sublist_cons_iff, hxt] using hu
    refine ⟨u, huq, ?_, heq⟩
    intro hbad
    exact hnot (hbad.cons t)
  · rintro ⟨u, hu, hnot, heq⟩
    refine ⟨u, hu.cons t, ?_, heq⟩
    intro hbad
    have : (x :: xs).Sublist q := by
      simpa [List.sublist_cons_iff, hxt] using hbad
    exact hnot this
private theorem boundary_cons_same_nonempty {q zs : Word} {t z b : Bool} :
    Boundary (t :: q) b (t :: z :: zs) ↔ Boundary q b (z :: zs) := by
  constructor
  · rintro ⟨u, hu, hnot, heq⟩
    cases u with
    | nil => simp at heq
    | cons d ds =>
        have hdtail : t = d ∧ z :: zs = ds ++ [b] := by simpa using heq
        have hd : t = d := hdtail.1
        subst d
        refine ⟨ds, List.cons_sublist_cons.mp hu, ?_, hdtail.2⟩
        intro hbad
        exact hnot (List.Sublist.cons_cons t hbad)
  · rintro ⟨u, hu, hnot, heq⟩
    refine ⟨t :: u, List.Sublist.cons_cons t hu, ?_, by
      simpa using congrArg (List.cons t) heq⟩
    intro hbad
    exact hnot (List.cons_sublist_cons.mp hbad)
private theorem not_boundary_cons_singleton (q : Word) (t b : Bool) :
    ¬ Boundary (t :: q) b [t] := by
  rintro ⟨u, hu, hnot, heq⟩
  exact hnot (List.Sublist.cons_cons t (List.nil_sublist q))
theorem validCode_after_active (q : Word) (x cf : Bool) (xs : Word) :
    ValidCode q (!x) cf xs ↔ Boundary q (!cf) (x :: xs) := by
  induction q generalizing x cf xs with
  | nil =>
      cases x <;> cases cf <;> cases xs <;> simp [ValidCode, Boundary]
  | cons t q ih =>
      by_cases hxt : x = t
      · subst x
        cases xs with
        | nil =>
            simp only [ValidCode, Bool.not_eq_self, if_false]
            exact (iff_false_intro (not_boundary_cons_singleton q t (!cf))).symm
        | cons z zs =>
            simp only [ValidCode, Bool.not_eq_self, if_false]
            rw [boundary_cons_same_nonempty]
            exact ih z cf zs
      · have hnotx_eq_t : (!x) = t := by
          cases x <;> cases t <;> simp_all
        simp only [ValidCode, hnotx_eq_t, if_true]
        rw [boundary_cons_ne hxt]
        simpa [hnotx_eq_t] using ih x cf xs
theorem validCode_zero_start (v y : Word) :
    ValidCode (true :: false :: v) false false y ↔
      Boundary (false :: v) true y := by
  cases y with
  | nil =>
      simp [ValidCode, Boundary]
  | cons x xs =>
      change ValidCode (false :: v) (!x) false xs ↔
        Boundary (false :: v) true (x :: xs)
      exact validCode_after_active (false :: v) x false xs
theorem validCode_one_start (v y : Word) :
    ValidCode (true :: false :: v) true true y ↔ Boundary v false y := by
  cases y with
  | nil =>
      simp [ValidCode, Boundary]
  | cons x xs =>
      simp only [ValidCode, if_true, Bool.true_eq_false, if_false]
      simpa using validCode_after_active v x true xs
def wordsLe : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 =>
      wordsLe n ∪ (wordsLe n).image (fun w => false :: w) ∪
        (wordsLe n).image (fun w => true :: w)
theorem mem_wordsLe {n : ℕ} {w : Word} : w ∈ wordsLe n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordsLe, List.length_eq_zero_iff]
  | succ n ih =>
      cases w with
      | nil =>
          constructor
          · intro _
            simp
          · intro _
            simp only [wordsLe, Finset.mem_union]
            exact Or.inl (Or.inl ((ih (w := [])).mpr (Nat.zero_le n)))
      | cons b w =>
          cases b <;> simp [wordsLe, ih] <;> omega
noncomputable def validCodes (q : Word) (c cf : Bool) : Finset Word :=
  (wordsLe q.length).filter fun y => ValidCode q c cf y
noncomputable def negativeValidCodes (q : Word) (c cf : Bool) : Finset Word :=
  (validCodes q c cf).filter fun y => ones y < zeros y
theorem mem_validCodes {q y : Word} {c cf : Bool} :
    y ∈ validCodes q c cf ↔ ValidCode q c cf y := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨mem_wordsLe.mpr (validCode_length_le h), h⟩
theorem mem_negativeValidCodes {q y : Word} {c cf : Bool} :
    y ∈ negativeValidCodes q c cf ↔
      ValidCode q c cf y ∧ ones y < zeros y := by
  classical
  simp [negativeValidCodes, mem_validCodes]
noncomputable def cyclicNegativeCount (q : Word) : ℕ :=
  (∑ y ∈ negativeValidCodes q false false,
      codeMultiplicity q false false y) +
  (∑ y ∈ negativeValidCodes q true true,
      codeMultiplicity q true true y)
theorem boundary_length_le {q y : Word} {b : Bool} (h : Boundary q b y) :
    y.length ≤ q.length + 1 := by
  rcases h with ⟨u, hu, _, rfl⟩
  simpa using Nat.add_le_add_right hu.length_le 1
theorem negativeValidCodes_zero_start (v : Word) :
    negativeValidCodes (true :: false :: v) false false =
      (boundaryFinset (false :: v) true).filter fun y => ones y < zeros y := by
  classical
  ext y
  simp only [mem_negativeValidCodes, Finset.mem_filter, mem_boundaryFinset]
  rw [validCode_zero_start]
theorem negativeValidCodes_one_start (v : Word) :
    negativeValidCodes (true :: false :: v) true true =
      (boundaryFinset v false).filter fun y => ones y < zeros y := by
  classical
  ext y
  simp only [mem_negativeValidCodes, Finset.mem_filter, mem_boundaryFinset]
  rw [validCode_one_start]
theorem cyclicNegativeCount_special (v : Word) :
    cyclicNegativeCount (true :: false :: v) =
      (∑ y ∈ (boundaryFinset (false :: v) true).filter (fun y => ones y < zeros y),
        2 ^ ((v.length + 2) - y.length)) +
      (∑ y ∈ (boundaryFinset v false).filter (fun y => ones y < zeros y),
        2 ^ ((v.length + 2) - y.length)) := by
  rw [cyclicNegativeCount, negativeValidCodes_zero_start,
    negativeValidCodes_one_start]
  apply congrArg₂ (.+.)
  · apply Finset.sum_congr rfl
    intro y hy
    apply codeMultiplicity_of_valid
    exact (validCode_zero_start v y).mpr (mem_boundaryFinset.mp (Finset.mem_filter.mp hy).1)
  · apply Finset.sum_congr rfl
    intro y hy
    apply codeMultiplicity_of_valid
    exact (validCode_one_start v y).mpr (mem_boundaryFinset.mp (Finset.mem_filter.mp hy).1)
theorem phiNeg_Benum (q : Word) (b : Bool) :
    phiNeg (Benum q b) =
      ∑ y ∈ (boundaryFinset q b).filter (fun y => ones y < zeros y),
        1 / (2 : ℚ) ^ y.length := by
  rw [Benum, phiNeg_enumerator, ← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  rw [zeros_add_ones]
theorem cast_pow_sub_div_pow (k m : ℕ) (hm : m ≤ k) :
    (2 : ℚ) ^ (k - m) / (2 : ℚ) ^ k = 1 / (2 : ℚ) ^ m := by
  rw [show k = (k - m) + m by omega, pow_add]
  field_simp
  congr 1
  omega
theorem cyclicNegativeCount_special_normalized (v : Word) :
    (cyclicNegativeCount (true :: false :: v) : ℚ) /
        (2 : ℚ) ^ (v.length + 2) = phiNeg (Cenum v) := by
  rw [cyclicNegativeCount_special, Cenum, phiNeg_add, phiNeg_Benum,
    phiNeg_Benum]
  push_cast
  rw [add_div]
  congr 1
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y hy
    apply cast_pow_sub_div_pow
    have hlen := boundary_length_le (mem_boundaryFinset.mp (Finset.mem_filter.mp hy).1)
    simp only [List.length_cons] at hlen ⊢
    omega
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y hy
    apply cast_pow_sub_div_pow
    have hlen := boundary_length_le (mem_boundaryFinset.mp (Finset.mem_filter.mp hy).1)
    omega
theorem cyclicNegativeCount_special_bound (v : Word) :
    cyclicNegativeCount (true :: false :: v) ≤ 2 ^ (v.length + 1) := by
  have hphi := cross_boundary_halfplane_bound v
  have hnorm := cyclicNegativeCount_special_normalized v
  rw [← hnorm] at hphi
  have hpow : (0 : ℚ) < (2 : ℚ) ^ (v.length + 2) := by positivity
  have hq : (cyclicNegativeCount (true :: false :: v) : ℚ) ≤
      (2 : ℚ) ^ (v.length + 1) := by
    rw [div_le_iff₀ hpow] at hphi
    rw [show v.length + 2 = (v.length + 1) + 1 by omega, pow_succ] at hphi
    norm_num at hphi ⊢
    linarith
  exact_mod_cast hq
structure CarryRun where
  output : Word
  code : Word
  carry : Bool
deriving DecidableEq
def carryRun : Word → Bool → Word → CarryRun
  | [], c, _ => ⟨[], [], c⟩
  | _ :: _, c, [] => ⟨[], [], c⟩
  | t :: q, c, a :: A =>
      if c = t then
        let r := carryRun q c A
        ⟨a :: r.output, r.code, r.carry⟩
      else
        let r := carryRun q a A
        ⟨(!a) :: r.output, (!a) :: r.code, r.carry⟩
def wordsExact : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 =>
      (wordsExact n).image (fun w => false :: w) ∪
        (wordsExact n).image (fun w => true :: w)
theorem mem_wordsExact {n : ℕ} {w : Word} : w ∈ wordsExact n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [wordsExact, List.length_eq_zero_iff]
  | succ n ih =>
      cases w with
      | nil => simp [wordsExact]
      | cons b w => cases b <;> simp [wordsExact, ih]
noncomputable def codeFiber (q : Word) (c cf : Bool) (y : Word) : Finset Word :=
  (wordsExact q.length).filter fun A =>
    (carryRun q c A).code = y ∧ (carryRun q c A).carry = cf
theorem mem_codeFiber {q A y : Word} {c cf : Bool} :
    A ∈ codeFiber q c cf y ↔
      A.length = q.length ∧ (carryRun q c A).code = y ∧
        (carryRun q c A).carry = cf := by
  classical
  simp [codeFiber, mem_wordsExact]
private theorem cons_false_ne_cons_true (S T : Finset Word) :
    Disjoint (S.image fun w => false :: w) (T.image fun w => true :: w) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw₀ hw₁
  rcases Finset.mem_image.mp hw₀ with ⟨u, _, rfl⟩
  simp at hw₁
theorem codeFiber_inactive (q : Word) (t cf : Bool) (y : Word) :
    codeFiber (t :: q) t cf y =
      (codeFiber q t cf y).image (fun A => false :: A) ∪
        (codeFiber q t cf y).image (fun A => true :: A) := by
  classical
  ext A
  cases A with
  | nil => simp [mem_codeFiber]
  | cons a A =>
      cases a <;> simp [mem_codeFiber, carryRun]
theorem codeFiber_active_nil (q : Word) (t c cf : Bool) (hct : c ≠ t) :
    codeFiber (t :: q) c cf [] = ∅ := by
  classical
  ext A
  cases A with
  | nil => simp [mem_codeFiber]
  | cons a A => cases a <;> cases c <;> cases t <;> simp_all [mem_codeFiber, carryRun]
theorem codeFiber_active_cons (q : Word) (t c cf x : Bool) (xs : Word)
    (hct : c ≠ t) :
    codeFiber (t :: q) c cf (x :: xs) =
      (codeFiber q (!x) cf xs).image (fun A => (!x) :: A) := by
  classical
  ext A
  cases A with
  | nil => simp [mem_codeFiber]
  | cons a A =>
      cases a <;> cases x <;> cases c <;> cases t <;>
        simp_all [mem_codeFiber, carryRun]
theorem card_codeFiber (q y : Word) (c cf : Bool) :
    (codeFiber q c cf y).card = codeMultiplicity q c cf y := by
  induction q generalizing c y with
  | nil =>
      cases y <;> cases c <;> cases cf <;> simp [codeFiber, codeMultiplicity,
        wordsExact, carryRun]
  | cons t q ih =>
      by_cases hct : c = t
      · subst c
        rw [codeFiber_inactive, Finset.card_union_of_disjoint
          (cons_false_ne_cons_true _ _)]
        rw [Finset.card_image_of_injective _ List.cons_injective,
          Finset.card_image_of_injective _ List.cons_injective]
        rw [ih]
        cases y <;> rw [codeMultiplicity]
        all_goals simp
        all_goals omega
      · cases y with
        | nil =>
            rw [codeFiber_active_nil q t c cf hct]
            simp [codeMultiplicity, hct]
        | cons x xs =>
            rw [codeFiber_active_cons q t c cf x xs hct]
            rw [Finset.card_image_of_injective _ List.cons_injective, ih]
            rw [codeMultiplicity]
            simp [hct]
noncomputable def cyclicInputs (q : Word) (c : Bool) : Finset Word :=
  (wordsExact q.length).filter fun A =>
    (carryRun q c A).carry = c ∧
      ones (carryRun q c A).code < zeros (carryRun q c A).code
noncomputable def cyclicInputCount (q : Word) : ℕ :=
  (cyclicInputs q false).card + (cyclicInputs q true).card
theorem carryRun_code_valid {q A : Word} {c : Bool} (hA : A.length = q.length) :
    ValidCode q c (carryRun q c A).carry (carryRun q c A).code := by
  induction q generalizing c A with
  | nil =>
      have : A = [] := List.length_eq_zero_iff.mp (by simpa using hA)
      subst A
      simp [carryRun, ValidCode]
  | cons t q ih =>
      cases A with
      | nil => simp at hA
      | cons a A =>
          have hlen : A.length = q.length := by simpa using hA
          by_cases hct : c = t
          · simp only [carryRun, hct, if_true, ValidCode]
            exact ih hlen
          · simp only [carryRun, hct, if_false, ValidCode]
            simpa using (ih (c := a) hlen)
private theorem cyclicInputs_fiber (q : Word) (c : Bool)
    (y : Word) (hy : y ∈ negativeValidCodes q c c) :
    (cyclicInputs q c).filter (fun A => (carryRun q c A).code = y) =
      codeFiber q c c y := by
  classical
  ext A
  rcases mem_negativeValidCodes.mp hy with ⟨_, hyneg⟩
  simp only [Finset.mem_filter, cyclicInputs, mem_wordsExact, mem_codeFiber]
  constructor
  · rintro ⟨⟨hA, hcarry, hneg⟩, hcode⟩
    exact ⟨hA, hcode, hcarry⟩
  · rintro ⟨hA, hcode, hcarry⟩
    exact ⟨⟨hA, hcarry, hcode ▸ hyneg⟩, hcode⟩
theorem card_cyclicInputs (q : Word) (c : Bool) :
    (cyclicInputs q c).card =
      ∑ y ∈ negativeValidCodes q c c, codeMultiplicity q c c y := by
  classical
  have hmap : ∀ A ∈ cyclicInputs q c,
      (carryRun q c A).code ∈ negativeValidCodes q c c := by
    intro A hA
    rcases Finset.mem_filter.mp hA with ⟨hAlen, hcarry, hneg⟩
    have hlen := mem_wordsExact.mp hAlen
    have hv := carryRun_code_valid (c := c) hlen
    rw [hcarry] at hv
    exact mem_negativeValidCodes.mpr ⟨hv, hneg⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap (fun _A => (1 : ℕ))
  simp only [Finset.sum_const, nsmul_one, Nat.cast_id] at hfiber
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro y hy
  rw [cyclicInputs_fiber q c y hy, card_codeFiber]
theorem cyclicInputCount_eq (q : Word) : cyclicInputCount q = cyclicNegativeCount q := by
  rw [cyclicInputCount, cyclicNegativeCount, card_cyclicInputs, card_cyclicInputs]
theorem carryRun_append (q₁ q₂ A₁ A₂ : Word) (c : Bool)
    (hlen : A₁.length = q₁.length) :
    carryRun (q₁ ++ q₂) c (A₁ ++ A₂) =
      let r₁ := carryRun q₁ c A₁
      let r₂ := carryRun q₂ r₁.carry A₂
      ⟨r₁.output ++ r₂.output, r₁.code ++ r₂.code, r₂.carry⟩ := by
  induction q₁ generalizing c A₁ with
  | nil =>
      have : A₁ = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst A₁
      simp [carryRun]
  | cons t q ih =>
      cases A₁ with
      | nil => simp at hlen
      | cons a A =>
          have htail : A.length = q.length := by simpa using hlen
          by_cases hct : c = t
          · simp only [List.cons_append, carryRun, hct, if_true]
            rw [ih (c := t) (A₁ := A) htail]
          · simp only [List.cons_append, carryRun, hct, if_false]
            rw [ih (c := a) (A₁ := A) htail]
def stepCarry (t c a : Bool) : Bool := if c = t then c else a
theorem carryRun_cons (t : Bool) (q : Word) (c a : Bool) (A : Word) :
    carryRun (t :: q) c (a :: A) =
      let r := carryRun q (stepCarry t c a) A
      if c = t then ⟨a :: r.output, r.code, r.carry⟩
      else ⟨(!a) :: r.output, (!a) :: r.code, r.carry⟩ := by
  by_cases h : c = t <;> simp [carryRun, stepCarry, h]
noncomputable def cyclicPairs (q : Word) : Finset ((c : Bool) × Word) :=
  Finset.univ.sigma fun c => cyclicInputs q c
theorem card_cyclicPairs (q : Word) : (cyclicPairs q).card = cyclicInputCount q := by
  rw [cyclicPairs, Finset.card_sigma, cyclicInputCount]
  simp
  omega
theorem mem_cyclicPairs {q : Word} {p : (c : Bool) × Word} :
    p ∈ cyclicPairs q ↔ p.2 ∈ cyclicInputs q p.1 := by
  classical
  simp [cyclicPairs]
def rotatePair (t : Bool) : ((c : Bool) × Word) → ((c : Bool) × Word)
  | ⟨c, []⟩ => ⟨c, []⟩
  | ⟨c, a :: A⟩ => ⟨stepCarry t c a, A ++ [a]⟩
theorem carryRun_rotate_closed {t c a : Bool} {q A : Word}
    (hlen : A.length = q.length)
    (hclosed : (carryRun (t :: q) c (a :: A)).carry = c) :
    let c₁ := stepCarry t c a
    let r := carryRun (q ++ [t]) c₁ (A ++ [a])
    r.carry = c₁ ∧
      ones r.code = ones (carryRun (t :: q) c (a :: A)).code ∧
      zeros r.code = zeros (carryRun (t :: q) c (a :: A)).code := by
  dsimp only
  rw [carryRun_append q [t] A [a] (stepCarry t c a) hlen]
  by_cases hct : c = t
  · subst c
    simp only [carryRun, stepCarry] at hclosed ⊢
    simp only [if_true] at hclosed ⊢
    rw [hclosed]
    simp [ones, zeros, List.count_append]
  · simp only [carryRun_cons, stepCarry, hct, if_false] at hclosed ⊢
    have htail : (carryRun q a A).carry = c := hclosed
    rw [htail]
    simp [carryRun, hct, zeros, ones, List.count_append, List.count_cons]
theorem rotatePair_mem {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (t :: q)) : rotatePair t p ∈ cyclicPairs (q ++ [t]) := by
  classical
  rcases p with ⟨c, A⟩
  rw [mem_cyclicPairs] at hp ⊢
  change A ∈ cyclicInputs (t :: q) c at hp
  rcases Finset.mem_filter.mp hp with ⟨hA, hclosed, hneg⟩
  have hlenfull := mem_wordsExact.mp hA
  cases A with
  | nil => simp at hlenfull
  | cons a A =>
      change A ++ [a] ∈ cyclicInputs (q ++ [t]) (stepCarry t c a)
      have hlen : A.length = q.length := by simpa using hlenfull
      rcases carryRun_rotate_closed hlen hclosed with ⟨hclosed', hone, hzero⟩
      apply Finset.mem_filter.mpr
      refine ⟨mem_wordsExact.mpr (by simp [hlen]), hclosed', ?_⟩
      simpa [hone, hzero] using hneg
def unrotatePair (q : Word) : ((c : Bool) × Word) → ((c : Bool) × Word)
  | ⟨c₁, R⟩ =>
      if h : R = [] then ⟨c₁, []⟩
      else
        let a := R.getLast h
        let A := R.dropLast
        let c := (carryRun q c₁ A).carry
        ⟨c, a :: A⟩
theorem unrotate_rotate {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (t :: q)) : unrotatePair q (rotatePair t p) = p := by
  classical
  rcases p with ⟨c, R⟩
  rw [mem_cyclicPairs] at hp
  change R ∈ cyclicInputs (t :: q) c at hp
  rcases Finset.mem_filter.mp hp with ⟨hR, hclosed, hneg⟩
  have hlenfull := mem_wordsExact.mp hR
  cases R with
  | nil => simp at hlenfull
  | cons a A =>
      have hlen : A.length = q.length := by simpa using hlenfull
      by_cases hct : c = t
      · subst c
        have htail : (carryRun q t A).carry = t := by
          simpa [carryRun_cons, stepCarry] using hclosed
        simp [rotatePair, unrotatePair, stepCarry, htail]
      · have htail : (carryRun q a A).carry = c := by
          simpa [carryRun_cons, stepCarry, hct] using hclosed
        simp [rotatePair, unrotatePair, stepCarry, hct, htail]
theorem unrotatePair_mem_and_rotate {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (q ++ [t])) :
    unrotatePair q p ∈ cyclicPairs (t :: q) ∧
      rotatePair t (unrotatePair q p) = p := by
  classical
  rcases p with ⟨c₁, R⟩
  rw [mem_cyclicPairs] at hp ⊢
  change R ∈ cyclicInputs (q ++ [t]) c₁ at hp
  rcases Finset.mem_filter.mp hp with ⟨hR, hclosed, hneg⟩
  have hlenfull := mem_wordsExact.mp hR
  have hRne : R ≠ [] := by
    intro h
    subst R
    simp at hlenfull
  let a := R.getLast hRne
  let A := R.dropLast
  have hdecomp : A ++ [a] = R := by
    exact List.dropLast_append_getLast hRne
  have hlen : A.length = q.length := by
    have := congrArg List.length hdecomp
    simp only [List.length_append, List.length_singleton] at this
    simp only [List.length_append, List.length_singleton] at hlenfull
    omega
  let c := (carryRun q c₁ A).carry
  have happ := carryRun_append q [t] A [a] c₁ hlen
  dsimp only at happ
  have hlast : (carryRun [t] c [a]).carry = c₁ := by
    have hc := congrArg CarryRun.carry happ
    rw [hdecomp, hclosed] at hc
    simpa [c] using hc.symm
  have hstep : stepCarry t c a = c₁ := by
    by_cases hct : c = t <;> simp [carryRun, stepCarry, hct] at hlast ⊢
    all_goals exact hlast
  have horig_closed : (carryRun (t :: q) c (a :: A)).carry = c := by
    rw [carryRun_cons]
    simp only [hstep]
    split <;> rfl
  have hrot := carryRun_rotate_closed hlen horig_closed
  dsimp only at hrot
  rw [hstep, hdecomp] at hrot
  rcases hrot with ⟨_, hone, hzero⟩
  constructor
  · simp only [unrotatePair, dif_neg hRne]
    change a :: A ∈ cyclicInputs (t :: q) c
    apply Finset.mem_filter.mpr
    refine ⟨mem_wordsExact.mpr (by simp [hlen]), horig_closed, ?_⟩
    omega
  · simp [unrotatePair, hRne, rotatePair, hstep, hdecomp, a, A, c]
theorem unrotatePair_mem {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (q ++ [t])) : unrotatePair q p ∈ cyclicPairs (t :: q) :=
  (unrotatePair_mem_and_rotate hp).1
theorem rotate_unrotate {t : Bool} {q : Word} {p : (c : Bool) × Word}
    (hp : p ∈ cyclicPairs (q ++ [t])) : rotatePair t (unrotatePair q p) = p :=
  (unrotatePair_mem_and_rotate hp).2
theorem cyclicInputCount_rotate (t : Bool) (q : Word) :
    cyclicInputCount (t :: q) = cyclicInputCount (q ++ [t]) := by
  rw [← card_cyclicPairs, ← card_cyclicPairs]
  apply Finset.card_bij (fun p _ => rotatePair t p)
  · exact fun p hp => rotatePair_mem hp
  · intro p₁ hp₁ p₂ hp₂ heq
    have h₁ := unrotate_rotate hp₁
    have h₂ := unrotate_rotate hp₂
    rw [← h₁, ← h₂, heq]
  · intro p hp
    exact ⟨unrotatePair q p, unrotatePair_mem hp, rotate_unrotate hp⟩
theorem cyclicInputCount_append_comm (a b : Word) :
    cyclicInputCount (a ++ b) = cyclicInputCount (b ++ a) := by
  induction a generalizing b with
  | nil => simp
  | cons t a ih =>
      calc
        cyclicInputCount ((t :: a) ++ b) =
            cyclicInputCount ((a ++ b) ++ [t]) := by
              simpa only [List.cons_append] using cyclicInputCount_rotate t (a ++ b)
        _ = cyclicInputCount ((b ++ [t]) ++ a) := by
              simpa only [List.append_assoc] using ih (b ++ [t])
        _ = cyclicInputCount (b ++ t :: a) := by
              simp only [List.append_assoc, List.singleton_append]
private theorem exists_true_false_after_start (r : Word) (hfalse : false ∈ r) :
    ∃ a b, true :: r = a ++ true :: false :: b := by
  induction r with
  | nil => simp at hfalse
  | cons x r ih =>
      cases x
      · exact ⟨[], r, rfl⟩
      · have htail : false ∈ r := by simpa using hfalse
        obtain ⟨a, b, hab⟩ := ih htail
        exact ⟨true :: a, b, by simpa using congrArg (List.cons true) hab⟩
theorem exists_special_rotation (q : Word) (htrue : true ∈ q)
    (hfalse : false ∈ q) :
    ∃ v, cyclicInputCount q = cyclicInputCount (true :: false :: v) ∧
      q.length = v.length + 2 := by
  obtain ⟨l₁, l₂, hq⟩ := List.mem_iff_append.mp htrue
  have hfalse' : false ∈ l₂ ++ l₁ := by
    rw [hq] at hfalse
    simpa only [List.mem_append, List.mem_cons, Bool.false_eq_true, false_or, or_comm]
      using hfalse
  obtain ⟨a, b, hab⟩ := exists_true_false_after_start (l₂ ++ l₁) hfalse'
  have hrot₁ : cyclicInputCount q = cyclicInputCount (true :: (l₂ ++ l₁)) := by
    rw [hq]
    simpa only [List.cons_append, List.append_assoc] using
      cyclicInputCount_append_comm l₁ (true :: l₂)
  have hrot₂ : cyclicInputCount (true :: (l₂ ++ l₁)) =
      cyclicInputCount (true :: false :: (b ++ a)) := by
    rw [hab]
    simpa only [List.cons_append, List.append_assoc] using
      cyclicInputCount_append_comm a (true :: false :: b)
  refine ⟨b ++ a, hrot₁.trans hrot₂, ?_⟩
  have hlen := congrArg List.length hq
  have hlen' := congrArg List.length hab
  simp only [List.length_append, List.length_cons] at hlen hlen' ⊢
  omega
theorem cyclicInputCount_bound_of_nonconstant (q : Word)
    (htrue : true ∈ q) (hfalse : false ∈ q) :
    cyclicInputCount q ≤ 2 ^ (q.length - 1) := by
  obtain ⟨v, hcount, hlen⟩ := exists_special_rotation q htrue hfalse
  rw [hcount, cyclicInputCount_eq, hlen]
  rw [show v.length + 2 - 1 = v.length + 1 by omega]
  exact cyclicNegativeCount_special_bound v
end TuDeng.FirstExit
end
section
namespace TuDeng.FirstExit
open scoped BigOperators
def wordValue : Word → ℕ
  | [] => 0
  | b :: w => Nat.bit b (wordValue w)
def bitsWord : ℕ → ℕ → Word
  | 0, _ => []
  | k + 1, n => n.testBit 0 :: bitsWord k (n >>> 1)
@[simp] theorem length_bitsWord (k n : ℕ) : (bitsWord k n).length = k := by
  induction k generalizing n <;> simp [bitsWord, *]
theorem wordValue_lt_pow (w : Word) : wordValue w < 2 ^ w.length := by
  induction w with
  | nil => simp [wordValue]
  | cons b w ih =>
      cases b <;> simp [wordValue, Nat.bit_false, Nat.bit_true, pow_succ] <;> omega
theorem wordValue_bitsWord {k n : ℕ} (hn : n < 2 ^ k) :
    wordValue (bitsWord k n) = n := by
  induction k generalizing n with
  | zero =>
      have : n = 0 := by simpa using hn
      subst n
      rfl
  | succ k ih =>
      have hshift : n >>> 1 < 2 ^ k := by
        rw [Nat.shiftRight_eq_div_pow]
        simp only [pow_one]
        omega
      simp only [bitsWord, wordValue]
      rw [ih hshift]
      exact Nat.bit_testBit_zero_shiftRight_one n
theorem bitsWord_wordValue (w : Word) : bitsWord w.length (wordValue w) = w := by
  induction w with
  | nil => simp [bitsWord, wordValue]
  | cons b w ih =>
      simp [bitsWord, wordValue, Nat.testBit_bit_zero, Nat.bit_shiftRight_one, ih]
theorem bitsWord_injective_on {k m n : ℕ} (hm : m < 2 ^ k) (hn : n < 2 ^ k)
    (h : bitsWord k m = bitsWord k n) : m = n := by
  rw [← wordValue_bitsWord hm, ← wordValue_bitsWord hn, h]
theorem hammingWeight_succ (k n : ℕ) :
    TuDeng.hammingWeight (k + 1) n =
      (if n.testBit 0 then 1 else 0) + TuDeng.hammingWeight k (n >>> 1) := by
  simp only [TuDeng.hammingWeight, List.range_succ_eq_map, List.map_cons,
    List.map_map, List.sum_cons]
  apply congrArg₂ (.+.) rfl
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  change (if n.testBit (Nat.succ i) then 1 else 0) =
    if (n >>> 1).testBit i then 1 else 0
  rw [Nat.testBit_succ, Nat.shiftRight_eq_div_pow]
theorem ones_bitsWord_eq_hammingWeight (k n : ℕ) :
    ones (bitsWord k n) = TuDeng.hammingWeight k n := by
  induction k generalizing n with
  | zero => simp [bitsWord, ones, TuDeng.hammingWeight]
  | succ k ih =>
      rw [bitsWord, hammingWeight_succ]
      simp only [ones, List.count_cons]
      rw [show List.count true (bitsWord k (n >>> 1)) =
        TuDeng.hammingWeight k (n >>> 1) by exact ih _]
      cases hbit : n.testBit 0 <;> simp [hbit] <;> omega
theorem wordValue_not_add_one (w : Word) :
    wordValue (w.map (!·)) + wordValue w + 1 = 2 ^ w.length := by
  induction w with
  | nil => simp [wordValue]
  | cons b w ih =>
      cases b <;>
        simp [wordValue, Nat.bit_false, Nat.bit_true, pow_succ] <;> omega
theorem wordValue_not_add (w : Word) :
    wordValue (w.map (!·)) + wordValue w = 2 ^ w.length - 1 := by
  have h := wordValue_not_add_one w
  have hp : 0 < 2 ^ w.length := by positivity
  omega
theorem wordValue_not (w : Word) :
    wordValue (w.map (!·)) = 2 ^ w.length - 1 - wordValue w := by
  have h := wordValue_not_add w
  omega
theorem ones_map_not (w : Word) : ones (w.map (!·)) = zeros w := by
  induction w with
  | nil => simp [ones, zeros]
  | cons b w ih => cases b <;> simpa [ones, zeros] using ih
@[simp] theorem carryRun_output_length {q A : Word} {c : Bool}
    (hlen : A.length = q.length) : (carryRun q c A).output.length = q.length := by
  induction q generalizing c A with
  | nil =>
      have : A = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst A
      simp [carryRun]
  | cons t q ih =>
      cases A with
      | nil => simp at hlen
      | cons a A =>
          have htail : A.length = q.length := by simpa using hlen
          by_cases hct : c = t <;> simp [carryRun, hct, ih htail]
theorem carryRun_numeric {q A : Word} {c : Bool} (hlen : A.length = q.length) :
    wordValue (carryRun q c A).output +
        2 ^ q.length * (carryRun q c A).carry.toNat =
      wordValue A + wordValue q + c.toNat := by
  induction q generalizing c A with
  | nil =>
      have : A = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst A
      cases c <;> simp [carryRun, wordValue]
  | cons t q ih =>
      cases A with
      | nil => simp at hlen
      | cons a A =>
          have htail : A.length = q.length := by simpa using hlen
          by_cases hct : c = t
          · subst c
            have hrec := ih (c := t) htail
            cases t <;> cases a <;>
              simp [carryRun, wordValue, Nat.bit_false, Nat.bit_true, pow_succ] at hrec ⊢ <;>
              nlinarith
          · have hrec := ih (c := a) htail
            cases t <;> cases c
            all_goals try {simp at hct}
            all_goals cases a <;>
              simp [carryRun, wordValue, Nat.bit_false, Nat.bit_true, pow_succ] at hrec ⊢ <;>
              nlinarith
theorem carryRun_weight {q A : Word} {c : Bool} (hlen : A.length = q.length) :
    ones (carryRun q c A).output + zeros (carryRun q c A).code =
      ones A + ones (carryRun q c A).code := by
  induction q generalizing c A with
  | nil =>
      have : A = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst A
      simp [carryRun, ones, zeros]
  | cons t q ih =>
      cases A with
      | nil => simp at hlen
      | cons a A =>
          have htail : A.length = q.length := by simpa using hlen
          by_cases hct : c = t
          · have hrec := ih (c := c) htail
            cases a <;> simp [carryRun, hct, ones, zeros] at hrec ⊢ <;> omega
          · have hrec := ih (c := a) htail
            cases a <;> simp [carryRun, hct, ones, zeros] at hrec ⊢ <;> omega
theorem carryRun_negative_iff {q A : Word} {c : Bool} (hlen : A.length = q.length) :
    ones (carryRun q c A).code < zeros (carryRun q c A).code ↔
      ones (carryRun q c A).output < ones A := by
  have h := carryRun_weight (c := c) hlen
  omega
theorem wordValue_eq_zero_of_not_true {w : Word} (h : true ∉ w) : wordValue w = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      have hb : b = false := by cases b <;> simp_all
      subst b
      simp [wordValue, ih (by simp_all)]
theorem wordValue_eq_all_ones_of_not_false {w : Word} (h : false ∉ w) :
    wordValue w = 2 ^ w.length - 1 := by
  induction w with
  | nil => simp [wordValue]
  | cons b w ih =>
      have hb : b = true := by cases b <;> simp_all
      subst b
      have htail : false ∉ w := by simp_all
      rw [wordValue, ih htail]
      simp only [Nat.bit_true, List.length_cons, pow_succ]
      have hp : 0 < 2 ^ w.length := by positivity
      omega
theorem bitsWord_mem_true {k n : ℕ} (hn0 : 0 < n) (hn : n < 2 ^ k) :
    true ∈ bitsWord k n := by
  by_contra h
  have hv := wordValue_eq_zero_of_not_true h
  rw [wordValue_bitsWord hn] at hv
  omega
theorem bitsWord_mem_false {k n : ℕ} (hn : n < 2 ^ k - 1) :
    false ∈ bitsWord k n := by
  by_contra h
  have hv := wordValue_eq_all_ones_of_not_false h
  rw [wordValue_bitsWord (lt_trans hn (by omega))] at hv
  rw [length_bitsWord] at hv
  omega
theorem bitsWord_modulus_sub (k x : ℕ) (hx : x ≤ 2 ^ k - 1) :
    bitsWord k x = (bitsWord k (2 ^ k - 1 - x)).map (!·) := by
  let A := bitsWord k (2 ^ k - 1 - x)
  have hAval : wordValue A = 2 ^ k - 1 - x := by
    apply wordValue_bitsWord
    have hp : 0 < 2 ^ k := by positivity
    omega
  have hlen : A.length = k := length_bitsWord _ _
  have hnotval : wordValue (A.map (!·)) = x := by
    rw [wordValue_not, hlen, hAval]
    omega
  calc
    bitsWord k x = bitsWord (A.map (!·)).length (wordValue (A.map (!·))) := by
      rw [List.length_map, hlen, hnotval]
    _ = A.map (!·) := bitsWord_wordValue _
def chosenCarry (k A t : ℕ) : Bool := decide (2 ^ k - 1 ≤ A + t)
theorem chosenCarry_run {k A t : ℕ} (hk : 0 < k)
    (hA : A ≤ 2 ^ k - 1) (ht : t < 2 ^ k - 1) :
    let c := chosenCarry k A t
    let r := carryRun (bitsWord k t) c (bitsWord k A)
    r.carry = c ∧ wordValue r.output = (A + t) % (2 ^ k - 1) := by
  dsimp only
  let N := 2 ^ k - 1
  let c := chosenCarry k A t
  let r := carryRun (bitsWord k t) c (bitsWord k A)
  change r.carry = c ∧ wordValue r.output = (A + t) % N
  have hpow : 0 < 2 ^ k := by positivity
  have hN : 0 < N := by dsimp [N]; omega
  have hPN : 2 ^ k = N + 1 := by dsimp [N]; omega
  have htpow : t < 2 ^ k := by omega
  have hApow : A < 2 ^ k := by omega
  have hnum := carryRun_numeric (q := bitsWord k t) (A := bitsWord k A) (c := c)
    (by simp)
  rw [wordValue_bitsWord hApow, wordValue_bitsWord htpow, length_bitsWord] at hnum
  change wordValue r.output + 2 ^ k * r.carry.toNat = A + t + c.toNat at hnum
  have hout : wordValue r.output < 2 ^ k := by
    have hlenout : r.output.length = k := by
      simpa [r] using carryRun_output_length
        (q := bitsWord k t) (A := bitsWord k A) (c := c) (by simp)
    simpa [hlenout] using wordValue_lt_pow r.output
  by_cases hs : N ≤ A + t
  · have hc : c = true := by simp [c, chosenCarry, N, hs]
    have hsum : A + t < 2 * N := by omega
    have hcarry : r.carry = true := by
      by_contra h
      have : r.carry = false := Bool.eq_false_of_not_eq_true h
      rw [hc, this] at hnum
      norm_num at hnum
      change 2 ^ k - 1 ≤ A + t at hs
      omega
    refine ⟨hcarry.trans hc.symm, ?_⟩
    have houtval : wordValue r.output = A + t - N := by
      rw [hc, hcarry] at hnum
      norm_num at hnum
      dsimp [N]
      omega
    rw [houtval, Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
  · have hc : c = false := by simp [c, chosenCarry, N, hs]
    have hsum : A + t < N := by omega
    have hcarry : r.carry = false := by
      by_contra h
      have : r.carry = true := Bool.eq_true_of_not_eq_false h
      rw [hc, this] at hnum
      norm_num at hnum
      change A + t < 2 ^ k - 1 at hsum
      omega
    refine ⟨hcarry.trans hc.symm, ?_⟩
    have houtval : wordValue r.output = A + t := by
      rw [hc, hcarry] at hnum
      norm_num at hnum
      exact hnum
    rw [houtval, Nat.mod_eq_of_lt hsum]
theorem hamming_modulus_sub_add_ones (k x : ℕ) (hx : x ≤ 2 ^ k - 1) :
    TuDeng.hammingWeight k x + ones (bitsWord k (2 ^ k - 1 - x)) = k := by
  rw [← ones_bitsWord_eq_hammingWeight, bitsWord_modulus_sub k x hx,
    ones_map_not]
  have hcount := zeros_add_ones (bitsWord k (2 ^ k - 1 - x))
  rw [length_bitsWord] at hcount
  omega
theorem hamming_eq_ones_of_value {k n : ℕ} {w : Word}
    (hlen : w.length = k) (hval : wordValue w = n) :
    TuDeng.hammingWeight k n = ones w := by
  rw [← ones_bitsWord_eq_hammingWeight]
  calc
    ones (bitsWord k n) = ones (bitsWord w.length (wordValue w)) := by rw [hlen, hval]
    _ = ones w := by rw [bitsWord_wordValue]
noncomputable def tdFinset (k t : ℕ) : Finset ℕ :=
  (Finset.range (TuDeng.modulus k)).filter fun x =>
    TuDeng.hammingWeight k x + TuDeng.hammingWeight k (TuDeng.partner k t x) ≤ k - 1
theorem tuDengCount_eq_card (k t : ℕ) :
    TuDeng.tuDengCount k t = (tdFinset k t).card := by
  have hnodup :
      ((List.range (TuDeng.modulus k)).filter (fun x =>
        TuDeng.hammingWeight k x +
          TuDeng.hammingWeight k (TuDeng.partner k t x) ≤ k - 1)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hcard := List.toFinset_card_of_nodup hnodup
  rw [List.toFinset_filter, List.toFinset_range] at hcard
  simpa [TuDeng.tuDengCount, tdFinset] using hcard.symm
def originalToPair (k t x : ℕ) : ((c : Bool) × Word) :=
  let N := 2 ^ k - 1
  let A := N - x
  ⟨chosenCarry k A t, bitsWord k A⟩
theorem partner_eq_A_mod {k t x : ℕ} (hx : x ≤ 2 ^ k - 1) :
    TuDeng.partner k t x = (2 ^ k - 1 - x + t) % (2 ^ k - 1) := by
  unfold TuDeng.partner TuDeng.modulus
  congr 1
  omega
theorem originalToPair_mem {k t x : ℕ} (hk : 0 < k)
    (ht : t < 2 ^ k - 1) (hx : x ∈ tdFinset k t) :
    originalToPair k t x ∈ cyclicPairs (bitsWord k t) := by
  classical
  rcases Finset.mem_filter.mp hx with ⟨hxrange, hxweight⟩
  have hxlt : x < 2 ^ k - 1 := by simpa [TuDeng.modulus] using Finset.mem_range.mp hxrange
  let N := 2 ^ k - 1
  let A := N - x
  let c := chosenCarry k A t
  let r := carryRun (bitsWord k t) c (bitsWord k A)
  have hA : A ≤ 2 ^ k - 1 := by dsimp [A, N]; omega
  have hrun := chosenCarry_run hk hA ht
  dsimp only at hrun
  change r.carry = c ∧ wordValue r.output = (A + t) % N at hrun
  rcases hrun with ⟨hclosed, houtval⟩
  have hpartner : TuDeng.partner k t x = (A + t) % N := by
    simpa [A, N, add_comm] using partner_eq_A_mod (k := k) (t := t) (le_of_lt hxlt)
  have houtweight : ones r.output = TuDeng.hammingWeight k (TuDeng.partner k t x) := by
    symm
    apply hamming_eq_ones_of_value (w := r.output)
    · simpa [r] using carryRun_output_length
        (q := bitsWord k t) (A := bitsWord k A) (c := c) (by simp)
    · rw [houtval, hpartner]
  have hcomp := hamming_modulus_sub_add_ones k x (le_of_lt hxlt)
  change TuDeng.hammingWeight k x + ones (bitsWord k A) = k at hcomp
  have hnegOut : ones r.output < ones (bitsWord k A) := by
    rw [houtweight]
    omega
  rw [mem_cyclicPairs]
  change bitsWord k A ∈ cyclicInputs (bitsWord k t) c
  apply Finset.mem_filter.mpr
  refine ⟨mem_wordsExact.mpr (by simp), hclosed, ?_⟩
  exact (carryRun_negative_iff (q := bitsWord k t) (A := bitsWord k A) (c := c)
    (by simp)).mpr hnegOut
def pairToOriginal (k : ℕ) (p : ((c : Bool) × Word)) : ℕ :=
  2 ^ k - 1 - wordValue p.2
theorem hammingWeight_modulus (k : ℕ) :
    TuDeng.hammingWeight k (2 ^ k - 1) = k := by
  have h := hamming_modulus_sub_add_ones k 0 (Nat.zero_le _)
  rw [show 2 ^ k - 1 - 0 = 2 ^ k - 1 by omega,
    ones_bitsWord_eq_hammingWeight] at h
  have hz : TuDeng.hammingWeight k 0 = 0 := by
    simp [TuDeng.hammingWeight]
  rw [hz, Nat.zero_add] at h
  exact h
theorem pairToOriginal_mem_and_inverse {k t : ℕ} (hk : 0 < k)
    (ht : t < 2 ^ k - 1) {p : ((c : Bool) × Word)}
    (hp : p ∈ cyclicPairs (bitsWord k t)) :
    pairToOriginal k p ∈ tdFinset k t ∧
      originalToPair k t (pairToOriginal k p) = p := by
  classical
  rcases p with ⟨c, W⟩
  rw [mem_cyclicPairs] at hp
  rcases Finset.mem_filter.mp hp with ⟨hWset, hclosed, hneg⟩
  have hWlen : W.length = k := by
    simpa using mem_wordsExact.mp hWset
  let A := wordValue W
  let r := carryRun (bitsWord k t) c W
  let B := wordValue r.output
  let N := 2 ^ k - 1
  have hApow : A < 2 ^ k := by
    dsimp [A]
    simpa [hWlen] using wordValue_lt_pow W
  have hA : A ≤ N := by dsimp [N]; omega
  have hrunlen : W.length = (bitsWord k t).length := by simp [hWlen]
  have hnegOut : ones r.output < ones W :=
    (carryRun_negative_iff (q := bitsWord k t) (A := W) (c := c) hrunlen).mp hneg
  have hApos : 0 < A := by
    by_contra h
    have hAzero : A = 0 := by omega
    have hw : TuDeng.hammingWeight k A = ones W :=
      hamming_eq_ones_of_value hWlen rfl
    rw [hAzero] at hw
    have : TuDeng.hammingWeight k 0 = 0 := by simp [TuDeng.hammingWeight]
    omega
  have houtlen : r.output.length = k := by
    simpa [r] using carryRun_output_length (q := bitsWord k t) (A := W) (c := c) hrunlen
  have hBpow : B < 2 ^ k := by
    dsimp [B]
    simpa [houtlen] using wordValue_lt_pow r.output
  have hB : B ≤ N := by dsimp [N]; omega
  have hBlt : B < N := by
    by_contra h
    have hBeq : B = N := by omega
    have hbweight : ones r.output = k := by
      rw [← hammingWeight_modulus k]
      symm
      apply hamming_eq_ones_of_value houtlen
      simpa [B, N] using hBeq
    have hwle : ones W ≤ k := by
      have hwle' : List.count true W ≤ W.length := List.count_le_length
      simpa [ones, hWlen] using hwle'
    omega
  have hnum := carryRun_numeric (q := bitsWord k t) (A := W) (c := c) hrunlen
  rw [hclosed, length_bitsWord] at hnum
  have htPow : t < 2 ^ k := by omega
  rw [wordValue_bitsWord htPow] at hnum
  change B + 2 ^ k * c.toNat = A + t + c.toNat at hnum
  have hPN : 2 ^ k = N + 1 := by
    dsimp [N]
    have : 0 < 2 ^ k := by positivity
    omega
  have hmod : (A + t) % N = B := by
    cases c
    · simp at hnum
      rw [← hnum, Nat.mod_eq_of_lt hBlt]
    · simp at hnum
      have heq : A + t = B + N := by omega
      rw [heq, Nat.add_mod, Nat.mod_eq_of_lt hBlt]
      simp [Nat.mod_self, Nat.add_mod, Nat.mod_eq_of_lt hBlt]
  let x := N - A
  have hxlt : x < N := by dsimp [x]; omega
  have hxle : x ≤ 2 ^ k - 1 := by dsimp [x, N]; omega
  have hpartner : TuDeng.partner k t x = B := by
    rw [partner_eq_A_mod hxle]
    change (N - x + t) % N = B
    have hNA : N - x = A := by dsimp [x]; omega
    rw [hNA, hmod]
  have hcomp := hamming_modulus_sub_add_ones k x hxle
  have hbitsA : bitsWord k A = W := by
    simpa [A, hWlen] using bitsWord_wordValue W
  change TuDeng.hammingWeight k x + ones (bitsWord k (2 ^ k - 1 - x)) = k at hcomp
  have hNx : 2 ^ k - 1 - x = A := by change N - x = A; dsimp [x]; omega
  rw [hNx, hbitsA] at hcomp
  have hbweight : TuDeng.hammingWeight k B = ones r.output :=
    hamming_eq_ones_of_value houtlen rfl
  have hweight : TuDeng.hammingWeight k x +
      TuDeng.hammingWeight k (TuDeng.partner k t x) ≤ k - 1 := by
    rw [hpartner, hbweight]
    omega
  have hxmem : x ∈ tdFinset k t := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by simpa [TuDeng.modulus, N] using hxlt), hweight⟩
  have hcarryChosen : chosenCarry k A t = c := by
    cases c
    · have hs : ¬ N ≤ A + t := by
        intro hs
        simp at hnum
        omega
      simp [chosenCarry, N, hs]
    · have hs : N ≤ A + t := by
        simp at hnum
        omega
      simp [chosenCarry, N, hs]
  constructor
  · simpa [pairToOriginal, x, N] using hxmem
  · change originalToPair k t x = ⟨c, W⟩
    simp only [originalToPair]
    rw [hNx, hcarryChosen, hbitsA]
theorem originalToPair_injective_on {k t x₁ x₂ : ℕ}
    (hx₁ : x₁ ∈ tdFinset k t) (hx₂ : x₂ ∈ tdFinset k t)
    (hp : originalToPair k t x₁ = originalToPair k t x₂) : x₁ = x₂ := by
  have hx₁lt : x₁ < 2 ^ k - 1 := by
    have := (Finset.mem_filter.mp hx₁).1
    simpa [TuDeng.modulus] using Finset.mem_range.mp this
  have hx₂lt : x₂ < 2 ^ k - 1 := by
    have := (Finset.mem_filter.mp hx₂).1
    simpa [TuDeng.modulus] using Finset.mem_range.mp this
  have hA₁pow : 2 ^ k - 1 - x₁ < 2 ^ k := by omega
  have hA₂pow : 2 ^ k - 1 - x₂ < 2 ^ k := by omega
  have hv := congrArg (fun p => wordValue p.2) hp
  change wordValue (bitsWord k (2 ^ k - 1 - x₁)) =
    wordValue (bitsWord k (2 ^ k - 1 - x₂)) at hv
  rw [wordValue_bitsWord hA₁pow, wordValue_bitsWord hA₂pow] at hv
  omega
theorem tdFinset_card_eq_cyclicPairs {k t : ℕ} (hk : 0 < k)
    (ht : t < 2 ^ k - 1) :
    (tdFinset k t).card = (cyclicPairs (bitsWord k t)).card := by
  classical
  apply Finset.card_bij (fun x _ => originalToPair k t x)
  · intro x hx
    exact originalToPair_mem hk ht hx
  · intro x₁ hx₁ x₂ hx₂ hp
    exact originalToPair_injective_on hx₁ hx₂ hp
  · intro p hp
    have hrev := pairToOriginal_mem_and_inverse hk ht hp
    exact ⟨pairToOriginal k p, hrev.1, hrev.2⟩
theorem tuDengCount_eq_cyclicInputCount {k t : ℕ} (hk : 0 < k)
    (ht : t < 2 ^ k - 1) :
    TuDeng.tuDengCount k t = cyclicInputCount (bitsWord k t) := by
  calc
    TuDeng.tuDengCount k t = (tdFinset k t).card := tuDengCount_eq_card k t
    _ = (cyclicPairs (bitsWord k t)).card := tdFinset_card_eq_cyclicPairs hk ht
    _ = cyclicInputCount (bitsWord k t) := card_cyclicPairs _
theorem tuDengCount_bound {k t : ℕ} (hk : 2 ≤ k)
    (ht₀ : 0 < t) (ht : t < 2 ^ k - 1) :
    TuDeng.tuDengCount k t ≤ 2 ^ (k - 1) := by
  rw [tuDengCount_eq_cyclicInputCount (by omega) ht]
  have htrue : true ∈ bitsWord k t := bitsWord_mem_true ht₀ (by omega)
  have hfalse : false ∈ bitsWord k t := bitsWord_mem_false ht
  simpa using cyclicInputCount_bound_of_nonconstant (bitsWord k t) htrue hfalse
theorem tu_deng_conjecture_full (k t : ℕ) (hk : 2 ≤ k) :
    TuDeng.TuDengConjecture k t := by
  intro ht₀ ht
  apply tuDengCount_bound hk ht₀
  simpa [TuDeng.modulus] using ht
end TuDeng.FirstExit
end

namespace KBridgeTD

lemma hw_zero (k : ℕ) : TuDeng.hammingWeight k 0 = 0 := by
  unfold TuDeng.hammingWeight
  simp

lemma hw_succ (k n : ℕ) : TuDeng.hammingWeight (k + 1) n =
    n % 2 + TuDeng.hammingWeight k (n / 2) := by
  unfold TuDeng.hammingWeight
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  congr 1
  · rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.testBit_zero, h]
  · congr 1
    apply List.map_congr_left
    intro i _
    simp [Function.comp, Nat.testBit_succ]

lemma bw_eq (k : ℕ) : ∀ n : ℕ, n < 2 ^ k →
    TuDengConjecture.binaryWeight n = TuDeng.hammingWeight k n := by
  induction k with
  | zero =>
    intro n hn
    have : n = 0 := by simpa using hn
    subst this
    simp [TuDengConjecture.binaryWeight, hw_zero]
  | succ k ih =>
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [TuDengConjecture.binaryWeight, hw_zero]
    · rw [hw_succ, ← ih (n / 2) (by rw [pow_succ] at hn; omega)]
      unfold TuDengConjecture.binaryWeight
      rw [Nat.digits_def' (by norm_num) hpos, List.sum_cons]

theorem bridge : type_of% @TuDengConjecture.tu_deng_conjecture := by
  intro k hk t ht
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  haveI : NeZero (2 ^ k - 1) := ⟨by omega⟩
  obtain ⟨t', ht'⟩ : ∃ t', t' = t.val := ⟨_, rfl⟩
  have ht0 : 0 < t' := by
    rw [ht']
    rcases Nat.eq_zero_or_pos t.val with h | h
    · exact absurd ((ZMod.val_eq_zero t).mp h) ht
    · exact h
  have htm : t' < 2 ^ k - 1 := ht' ▸ ZMod.val_lt t
  have hbound := TuDeng.FirstExit.tu_deng_conjecture_full k t' hk ht0 (by
    simpa [TuDeng.modulus] using htm)
  let T : Finset ℕ := (Finset.range (2 ^ k - 1)).filter (fun x =>
    TuDeng.hammingWeight k x + TuDeng.hammingWeight k (TuDeng.partner k t' x) ≤ k - 1)
  have hT : T.card = TuDeng.tuDengCount k t' := by
    unfold TuDeng.tuDengCount
    simp only [T, TuDeng.modulus]
    rfl
  have hval : ∀ x : ZMod (2 ^ k - 1), x.val < 2 ^ k := fun x => by
    have := ZMod.val_lt x
    omega
  calc _ ≤ (T : Set ℕ).ncard := by
        apply Set.ncard_le_ncard_of_injOn (fun p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) => p.1.val)
        · rintro ⟨a, b⟩ ⟨hab, hw⟩
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, T]
          refine ⟨ZMod.val_lt a, ?_⟩
          have hb : b = t - a := by rw [← hab]; ring
          have hp : TuDeng.partner k t' a.val = b.val := by
            unfold TuDeng.partner
            rw [TuDeng.modulus, hb]
            have hle : a.val ≤ t' + (2 ^ k - 1) := by have := ZMod.val_lt a; omega
            rw [← ZMod.val_natCast, Nat.cast_sub hle]
            simp [ht']
          rw [hp, ← bw_eq k _ (hval a), ← bw_eq k _ (hval b)]
          exact hw
        · rintro ⟨a, b⟩ ⟨hab, _⟩ ⟨c, d⟩ ⟨hcd, _⟩ hac
          simp only at hac
          have h1 : a = c := ZMod.val_injective _ hac
          have hb : b = t - a := by rw [← hab]; ring
          have hd : d = t - c := by rw [← hcd]; ring
          subst hb hd h1
          rfl
    _ = T.card := Set.ncard_coe_finset T
    _ = TuDeng.tuDengCount k t' := hT
    _ ≤ 2 ^ (k - 1) := hbound

end KBridgeTD

theorem OMA.solution : type_of% @TuDengConjecture.tu_deng_conjecture := KBridgeTD.bridge
