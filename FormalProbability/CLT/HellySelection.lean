import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.CDF
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences

/-!
# FormalProbability/CLT/HellySelection.lean

Compactness/Helly selection step for CDFs on rationals.
We extract a subsequence with pointwise convergence on `ℚ` and record the monotone limit.
-/

set_option linter.mathlibStandardSet false

open scoped Classical
open scoped Topology

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ProbabilityTheory

open MeasureTheory
open Filter

/-- CDF sequence viewed in the compact product `ℚ → Icc 0 1`. -/
def cdfSeq (μs : ℕ → ProbabilityMeasure ℝ) (n : ℕ) : ℚ → Set.Icc (0 : ℝ) 1 :=
  fun q =>
    ⟨cdf (μs n) (q : ℝ),
      ⟨cdf_nonneg (μ := (μs n : Measure ℝ)) (x := (q : ℝ)),
        cdf_le_one (μ := (μs n : Measure ℝ)) (x := (q : ℝ))⟩⟩

theorem exists_subseq_tendsto_cdf_rat (μs : ℕ → ProbabilityMeasure ℝ) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∃ F : ℚ → ℝ,
        (∀ q, 0 ≤ F q ∧ F q ≤ 1) ∧
        ∀ q : ℚ, Tendsto (fun n => cdf (μs (s n)) (q : ℝ)) atTop (𝓝 (F q)) := by
  classical
  -- Use sequential compactness of the product of compact intervals.
  have hsub :
      ∃ (F' : ℚ → Set.Icc (0 : ℝ) 1) (s : ℕ → ℕ),
        StrictMono s ∧ Tendsto (cdfSeq μs ∘ s) atTop (𝓝 F') := by
    simpa using (CompactSpace.tendsto_subseq (cdfSeq μs))
  rcases hsub with ⟨F', s, hs, h_tendsto⟩
  refine ⟨s, hs, (fun q => (F' q : ℝ)), ?_, ?_⟩
  · intro q
    exact (F' q).property
  · intro q
    have hcoord : Tendsto (fun n => cdfSeq μs (s n) q) atTop (𝓝 (F' q)) := by
      exact (tendsto_pi_nhds.1 h_tendsto) q
    have hcoord' :
        Tendsto (fun n => (cdfSeq μs (s n) q : ℝ)) atTop (𝓝 (F' q : ℝ)) :=
      (continuous_subtype_val.tendsto (x := F' q)).comp hcoord
    simpa [cdfSeq] using hcoord'

theorem monotone_limit_cdf_rat
    {μs : ℕ → ProbabilityMeasure ℝ} {s : ℕ → ℕ} {F : ℚ → ℝ}
    (hF : ∀ q : ℚ, Tendsto (fun n => cdf (μs (s n)) (q : ℝ)) atTop (𝓝 (F q))) :
    Monotone F := by
  intro q₁ q₂ hq
  have hq' : (q₁ : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hq
  have h_le : ∀ n, cdf (μs (s n)) (q₁ : ℝ) ≤ cdf (μs (s n)) (q₂ : ℝ) := by
    intro n
    have hmono := monotone_cdf (μ := (μs (s n) : Measure ℝ))
    exact hmono hq'
  exact le_of_tendsto_of_tendsto (hF q₁) (hF q₂) (Filter.Eventually.of_forall h_le)

/-- Right-limit extension of a rational function. -/
def ratLimit (F : ℚ → ℝ) (x : ℝ) : ℝ :=
  ⨅ q : {q : ℚ // x < q}, F q

lemma ratLimit_nonempty (x : ℝ) : Nonempty {q : ℚ // x < q} := by
  obtain ⟨q, hq⟩ := exists_rat_gt x
  exact ⟨⟨q, hq⟩⟩

lemma bddBelow_ratLimit {F : ℚ → ℝ} (hF_nonneg : ∀ q, 0 ≤ F q) (x : ℝ) :
    BddBelow (Set.range fun q : {q : ℚ // x < q} => F q) := by
  refine ⟨0, ?_⟩
  rintro y ⟨q, rfl⟩
  exact hF_nonneg q

lemma ratLimit_le_of_lt {F : ℚ → ℝ} (hF_nonneg : ∀ q, 0 ≤ F q) {x : ℝ} {q : ℚ}
    (hxq : x < q) : ratLimit F x ≤ F q := by
  have h_bdd := bddBelow_ratLimit (F := F) hF_nonneg x
  exact ciInf_le h_bdd ⟨q, hxq⟩

lemma ratLimit_nonneg {F : ℚ → ℝ} (hF_nonneg : ∀ q, 0 ≤ F q) (x : ℝ) :
    0 ≤ ratLimit F x := by
  have hnonempty : Nonempty {q : ℚ // x < q} := ratLimit_nonempty x
  haveI := hnonempty
  exact le_ciInf (fun q => hF_nonneg q)

lemma ratLimit_le_one {F : ℚ → ℝ} (hF_nonneg : ∀ q, 0 ≤ F q) (hF_le_one : ∀ q, F q ≤ 1)
    (x : ℝ) : ratLimit F x ≤ 1 := by
  obtain ⟨q, hxq⟩ := exists_rat_gt x
  exact (ratLimit_le_of_lt (F := F) hF_nonneg (x := x) (q := q) hxq).trans (hF_le_one q)

lemma monotone_ratLimit {F : ℚ → ℝ} (hF_nonneg : ∀ q, 0 ≤ F q) :
    Monotone (ratLimit F) := by
  intro x y hxy
  have hnonempty : Nonempty {q : ℚ // y < q} := ratLimit_nonempty y
  haveI := hnonempty
  refine le_ciInf ?_
  intro q
  have hxq : x < (q : ℚ) := lt_of_le_of_lt hxy q.property
  exact ratLimit_le_of_lt (F := F) hF_nonneg (x := x) (q := q) hxq

lemma le_ratLimit_of_mono {F : ℚ → ℝ} (hF_mono : Monotone F) {x : ℝ} {q : ℚ}
    (hxq : (q : ℝ) ≤ x) : F q ≤ ratLimit F x := by
  have hnonempty : Nonempty {r : ℚ // x < r} := ratLimit_nonempty x
  haveI := hnonempty
  refine le_ciInf ?_
  intro r
  have hqr' : (q : ℝ) < (r : ℚ) := lt_of_le_of_lt hxq r.property
  have hqr : q ≤ r := by
    exact_mod_cast (le_of_lt hqr')
  exact hF_mono hqr

lemma ratLimit_iInf_rat_gt_eq {F : ℚ → ℝ} (hF_nonneg : ∀ q, 0 ≤ F q) (x : ℝ) :
    (⨅ q : {q : ℚ // x < q}, ratLimit F q) = ratLimit F x := by
  have hmono : Monotone (ratLimit F) := monotone_ratLimit (F := F) hF_nonneg
  have hnonempty : Nonempty {q : ℚ // x < q} := ratLimit_nonempty x
  haveI := hnonempty
  have h_le : ratLimit F x ≤ ⨅ q : {q : ℚ // x < q}, ratLimit F q := by
    refine le_ciInf ?_
    intro q
    exact hmono (le_of_lt q.property)
  have h_bdd :
      BddBelow (Set.range fun q : {q : ℚ // x < q} => ratLimit F q) := by
    refine ⟨0, ?_⟩
    rintro y ⟨q, rfl⟩
    exact ratLimit_nonneg (F := F) hF_nonneg q
  have h_le' : (⨅ q : {q : ℚ // x < q}, ratLimit F q) ≤ ratLimit F x := by
    refine le_ciInf ?_
    intro r
    obtain ⟨q, hxq, hqr⟩ := exists_rat_btwn r.property
    have h_inf_le_q :
        (⨅ q' : {q' : ℚ // x < q'}, ratLimit F q') ≤ ratLimit F (q : ℝ) :=
      ciInf_le h_bdd ⟨q, hxq⟩
    have h_q_le_r : ratLimit F (q : ℝ) ≤ F r :=
      ratLimit_le_of_lt (F := F) hF_nonneg (x := (q : ℝ)) (q := r) hqr
    exact h_inf_le_q.trans h_q_le_r
  exact le_antisymm h_le' h_le

lemma continuousWithinAt_ratLimit_Ici {F : ℚ → ℝ} (hF_nonneg : ∀ q, 0 ≤ F q) (x : ℝ) :
    ContinuousWithinAt (ratLimit F) (Set.Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  have hmono : Monotone (ratLimit F) := monotone_ratLimit (F := F) hF_nonneg
  have h_eq : sInf (ratLimit F '' Set.Ioi x) = ratLimit F x := by
    rw [sInf_image']
    have h_iInf :
        (⨅ r : Set.Ioi x, ratLimit F r) =
          ⨅ q : {q : ℚ // x < q}, ratLimit F q := by
      refine Real.iInf_Ioi_eq_iInf_rat_gt x ?_ hmono
      refine ⟨0, ?_⟩
      rintro y ⟨r, -, rfl⟩
      exact ratLimit_nonneg (F := F) hF_nonneg r
    simpa [h_iInf] using (ratLimit_iInf_rat_gt_eq (F := F) hF_nonneg x)
  simpa [h_eq] using (Monotone.tendsto_nhdsGT hmono x)

/-- Stieltjes function built from a rational limit via right limits. -/
def ratStieltjes (F : ℚ → ℝ) (hF_nonneg : ∀ q, 0 ≤ F q) : StieltjesFunction ℝ :=
  { toFun := ratLimit F
    mono' := monotone_ratLimit (F := F) hF_nonneg
    right_continuous' := continuousWithinAt_ratLimit_Ici (F := F) hF_nonneg }

theorem tendsto_cdf_of_tendsto_cdf_rat
    {μs : ℕ → ProbabilityMeasure ℝ} {s : ℕ → ℕ} {F : ℚ → ℝ}
    (hF_nonneg : ∀ q, 0 ≤ F q)
    (hF_tendsto : ∀ q : ℚ,
      Tendsto (fun n => cdf (μs (s n)) (q : ℝ)) atTop (𝓝 (F q)))
    {x : ℝ} (h_cont : ContinuousAt (ratLimit F) x) :
    Tendsto (fun n => cdf (μs (s n)) x) atTop (𝓝 (ratLimit F x)) := by
  have hmono : Monotone (ratLimit F) := monotone_ratLimit (F := F) hF_nonneg
  refine (tendsto_order.2 ⟨?_, ?_⟩)
  · intro a ha
    have h_right :
        Function.rightLim (ratLimit F) x = ratLimit F x := by
      have hcontIci : ContinuousWithinAt (ratLimit F) (Set.Ici x) x :=
        continuousWithinAt_ratLimit_Ici (F := F) hF_nonneg x
      simpa using (ContinuousWithinAt.rightLim_eq (f := ratLimit F) (a := x) hcontIci)
    have h_left :
        Function.leftLim (ratLimit F) x = ratLimit F x := by
      have h_eq := (hmono.continuousAt_iff_leftLim_eq_rightLim).1 h_cont
      simpa [h_right] using h_eq
    have h_nebot : (𝓝[<] x) ≠ ⊥ := (inferInstance : NeBot (𝓝[<] x)).ne
    have h_leftSup :
        Function.leftLim (ratLimit F) x = sSup (ratLimit F '' Set.Iio x) :=
      (Monotone.leftLim_eq_sSup (hf := hmono) (x := x) h_nebot)
    have h_leftSup' : ratLimit F x = sSup (ratLimit F '' Set.Iio x) := by
      calc
        ratLimit F x = Function.leftLim (ratLimit F) x := by symm; exact h_left
        _ = sSup (ratLimit F '' Set.Iio x) := h_leftSup
    have ha' : a < sSup (ratLimit F '' Set.Iio x) := by
      simpa [h_leftSup'] using ha
    have h_nonempty : (ratLimit F '' Set.Iio x).Nonempty := by
      obtain ⟨y, hy⟩ := exists_rat_lt x
      exact ⟨ratLimit F y, ⟨y, hy, rfl⟩⟩
    rcases exists_lt_of_lt_csSup h_nonempty ha' with ⟨y, hy_mem, hay⟩
    rcases hy_mem with ⟨y, hy, rfl⟩
    have hy' : (y : ℝ) < x := by
      simpa [Set.mem_Iio] using hy
    obtain ⟨q, hqy, hqx⟩ := exists_rat_btwn hy'
    have h_le_q : ratLimit F (y : ℝ) ≤ F q :=
      ratLimit_le_of_lt (F := F) hF_nonneg (x := (y : ℝ)) (q := q) hqy
    have ha_q : a < F q := lt_of_lt_of_le hay h_le_q
    have h_event : ∀ᶠ n in atTop, a < cdf (μs (s n)) (q : ℝ) :=
      (tendsto_order.1 (hF_tendsto q)).1 a ha_q
    filter_upwards [h_event] with n hn
    have h_mono := monotone_cdf (μ := (μs (s n) : Measure ℝ))
    have hqx' : (q : ℝ) < x := by exact_mod_cast hqx
    exact lt_of_lt_of_le hn (h_mono (le_of_lt hqx'))
  · intro a ha
    have hnonempty : Nonempty {q : ℚ // x < q} := ratLimit_nonempty x
    haveI := hnonempty
    have h' : (⨅ q : {q : ℚ // x < q}, F q) < a := by
      simpa [ratLimit] using ha
    obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt (f := fun q : {q : ℚ // x < q} => F q) h'
    have h_event : ∀ᶠ n in atTop, cdf (μs (s n)) (q : ℝ) < a :=
      (tendsto_order.1 (hF_tendsto q)).2 a hq
    filter_upwards [h_event] with n hn
    have h_mono := monotone_cdf (μ := (μs (s n) : Measure ℝ))
    have hxq : (x : ℝ) ≤ (q : ℚ) := le_of_lt q.property
    exact lt_of_le_of_lt (h_mono hxq) hn

end ProbabilityTheory
