import OAI.Combinatorics.Sunflower.FixedBase
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter Real
open scoped BigOperators

namespace Erdos535

noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
    A.card = k}

private def smallExponents (y n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter (· ≤ y)

private def roughExponents (y n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter (fun p => ¬ p ≤ y)

private def staircase (f : ℕ →₀ ℕ) : Finset (ℕ × ℕ) :=
  (f.support.sigma (fun p => Finset.range (f p))).map (Equiv.sigmaEquivProd ℕ ℕ).toEmbedding

private theorem mem_staircase (f : ℕ →₀ ℕ) (p j : ℕ) :
    (p, j) ∈ staircase f ↔ j < f p := by
  rw [staircase]
  change (Equiv.sigmaEquivProd ℕ ℕ).toEmbedding ⟨p, j⟩ ∈ _ ↔ _
  rw [Finset.mem_map', Finset.mem_sigma, Finset.mem_range, Finsupp.mem_support_iff]
  exact ⟨And.right, fun h => ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt h), h⟩⟩

private theorem card_staircase (f : ℕ →₀ ℕ) :
    (staircase f).card = ∑ p ∈ f.support, f p := by
  simp [staircase, Finset.card_sigma]

private theorem staircase_injective : Function.Injective staircase := by
  intro f g h
  ext p
  apply le_antisymm
  · by_contra! hlt
    have hg : (p, g p) ∈ staircase f := (mem_staircase f p (g p)).mpr hlt
    rw [h, mem_staircase] at hg
    exact lt_irrefl _ hg
  · by_contra! hlt
    have hf : (p, f p) ∈ staircase g := (mem_staircase g p (f p)).mpr hlt
    rw [← h, mem_staircase] at hf
    exact lt_irrefl _ hf

private theorem staircase_inf (f g : ℕ →₀ ℕ) :
    staircase (f ⊓ g) = staircase f ∩ staircase g := by
  ext ⟨p, j⟩
  simp only [mem_staircase, Finset.mem_inter, Finsupp.inf_apply, lt_min_iff]

private theorem smallExponents_gcd (y : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    smallExponents y (Nat.gcd a b) = smallExponents y a ⊓ smallExponents y b := by
  ext p
  simp only [smallExponents, Nat.factorization_gcd ha hb, Finsupp.filter_apply, Finsupp.inf_apply]
  split <;> simp

private theorem roughExponents_gcd (y : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    roughExponents y (Nat.gcd a b) = roughExponents y a ⊓ roughExponents y b := by
  ext p
  simp only [roughExponents, Nat.factorization_gcd ha hb, Finsupp.filter_apply, Finsupp.inf_apply]
  split <;> simp

private theorem eq_of_split_eq {y a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hs : smallExponents y a = smallExponents y b)
    (hr : roughExponents y a = roughExponents y b) : a = b := by
  apply Nat.eq_of_factorization_eq' ha hb
  calc
    a.factorization = smallExponents y a + roughExponents y a :=
      (Finsupp.filter_add_filter_not _ _).symm
    _ = smallExponents y b + roughExponents y b := by rw [hs, hr]
    _ = b.factorization := Finsupp.filter_add_filter_not _ _

private theorem gcd_eq_of_fiber_inter {y a b c d : ℕ} {s : ℕ →₀ ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hsa : smallExponents y a = s) (hsb : smallExponents y b = s)
    (hsc : smallExponents y c = s) (hsd : smallExponents y d = s)
    (hinter : staircase (roughExponents y a) ∩ staircase (roughExponents y b) =
      staircase (roughExponents y c) ∩ staircase (roughExponents y d)) :
    Nat.gcd a b = Nat.gcd c d := by
  apply eq_of_split_eq (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hc)
  · rw [smallExponents_gcd y ha hb, smallExponents_gcd y hc hd, hsa, hsb, hsc, hsd]
  · apply staircase_injective
    simpa only [roughExponents_gcd y ha hb, roughExponents_gcd y hc hd, staircase_inf] using hinter

private theorem rough_height (y n : ℕ) (hn : n ≠ 0) :
    y ^ (staircase (roughExponents y n)).card ≤ n := by
  let e := roughExponents y n
  change y ^ (staircase e).card ≤ n
  have he : e ≤ n.factorization := by
    intro p
    change n.factorization.filter (fun p => ¬ p ≤ y) p ≤ n.factorization p
    rw [Finsupp.filter_apply]
    split <;> simp
  calc
    y ^ (staircase e).card = ∏ p ∈ e.support, y ^ (e p) := by
      rw [card_staircase, Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ p ∈ e.support, p ^ (e p) := by
      apply Finset.prod_le_prod'
      intro p hp
      apply Nat.pow_le_pow_left
      exact Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_pow_dvd_of_le_factorization he)

private def SunflowerFree {α : Type*} [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ T ⊆ F, T.card = r → ¬ ∃ U, (T : Set (Finset α)).Pairwise fun x y => x ∩ y = U

private theorem sunflowerFree_image {α : Type*} [DecidableEq α] {r : ℕ} {A : Finset ℕ}
    {encode : ℕ → Finset α} (hr : 2 ≤ r)
    (hA : ∀ S ⊆ A, S.card = r → ¬ ∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)
    (hinj : Set.InjOn encode A)
    (hcommon : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      encode a ∩ encode b = encode c ∩ encode d → Nat.gcd a b = Nat.gcd c d) :
    SunflowerFree r (A.image encode) := by
  classical
  intro T hT hcard hflower
  obtain ⟨U, hpair⟩ := hflower
  let S := A.filter fun a => encode a ∈ T
  have hSA : S ⊆ A := Finset.filter_subset _ _
  have hST : S.image encode = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp ha).2
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hT hx)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hx⟩, rfl⟩
  have hSInj : Set.InjOn encode S := fun _ ha _ hb heq => hinj (hSA ha) (hSA hb) heq
  have hSCard : S.card = r := by
    rw [← Finset.card_image_of_injOn hSInj, hST, hcard]
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  have hcore : ∀ {x y : ℕ}, x ∈ S → y ∈ S → x ≠ y → encode x ∩ encode y = U := by
    intro x y hx hy hxy
    exact hpair (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
      (fun heq => hxy (hSInj hx hy heq))
  apply hA S hSA hSCard
  refine ⟨Nat.gcd a b, ?_⟩
  intro x hx y hy hxy
  exact hcommon x (hSA hx) y (hSA hy) a (hSA ha) b (hSA hb)
    ((hcore hx hy hxy).trans (hcore ha hb hab).symm)

private theorem sunflowerFree_card_le_maxRank {α : Type*} [DecidableEq α]
    {r C k : ℕ} {F : Finset (Finset α)} (hC : 1 ≤ C)
    (huniform : ∀ (j : ℕ) (G : Finset (Finset α)), (∀ A ∈ G, A.card = j) →
      C ^ j < G.card → ∃ H ⊆ G, H.card = r ∧ ∃ K : Finset α,
        ∀ A ∈ H, ∀ B ∈ H, A ≠ B → A ∩ B = K)
    (hF : SunflowerFree r F) (hrank : ∀ A ∈ F, A.card ≤ k) :
    F.card ≤ (2 * C) ^ k := by
  have hsum := Finset.card_le_mul_card_image_of_maps_to (f := Finset.card) (s := F)
    (t := Finset.range (k + 1)) (fun A hA => Finset.mem_range.mpr (Nat.lt_succ_of_le (hrank A hA)))
    (C ^ k) (fun j hj => by
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      let G := F.filter fun A => A.card = j
      suffices G.card ≤ C ^ j from this.trans (pow_le_pow_right' hC hjk)
      by_contra hexcess
      obtain ⟨H, hHG, hHcard, K, hHK⟩ := huniform j G (fun A hA =>
        (Finset.mem_filter.mp hA).2) (Nat.lt_of_not_ge hexcess)
      apply hF H (hHG.trans (Finset.filter_subset _ _)) hHcard
      exact ⟨K, fun A hA B hB hne => hHK A hA B hB hne⟩)
  rw [Finset.card_range] at hsum
  calc
    F.card ≤ C ^ k * (k + 1) := hsum
    _ ≤ C ^ k * 2 ^ k := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.lt_two_pow_self))
    _ = (2 * C) ^ k := by rw [mul_pow, mul_comm]

open scoped Classical in
private theorem exists_maxRankSunflowerBound {r : ℕ} (hr : 3 ≤ r) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (k : ℕ) (F : Finset (Finset (ℕ × ℕ))),
      SunflowerFree r F → (∀ A ∈ F, A.card ≤ k) → F.card ≤ D ^ k := by
  obtain ⟨C, hC, huniform⟩ := OAI.Combinatorics.Sunflower.erdosRadoSunflower r hr
  refine ⟨2 * C, by omega, fun k F hF hrank => ?_⟩
  refine sunflowerFree_card_le_maxRank hC (fun j G hG hexcess => ?_) hF hrank
  obtain ⟨H, hHG, hHcard, K, hHK⟩ := huniform j (ℕ × ℕ) G hG hexcess
  refine ⟨H, hHG, hHcard, K, fun A hA B hB hAB => ?_⟩
  have heq := hHK A hA B hB hAB
  ext x
  rw [← heq]
  simp only [Finset.mem_inter]

private theorem cutoff_estimates :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      let y := ⌊Real.sqrt L⌋₊
      2 ≤ y ∧ 0 < Real.log L ∧ Real.log L ≤ 4 * Real.log (y : ℝ) ∧
        (y : ℝ) * Real.log (1 + L / Real.log 2) ≤ L / Real.log L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : ∀ᶠ L : ℝ in atTop,
      ‖Real.log L ^ (2 : ℝ)‖ ≤ (1 / 2 : ℝ) * ‖L ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (by norm_num)
  filter_upwards [hL.eventually (eventually_ge_atTop (4 : ℝ)),
    hL.eventually (eventually_ge_atTop (1 + (Real.log 2)⁻¹)), hL.eventually hpow] with N hfour hlarge hsmall
  dsimp only at hfour hlarge hsmall ⊢
  let L := Real.log (N : ℝ)
  let y := ⌊Real.sqrt L⌋₊
  change (4 : ℝ) ≤ L at hfour
  change 1 + (Real.log 2)⁻¹ ≤ L at hlarge
  change ‖Real.log L ^ (2 : ℝ)‖ ≤ (1 / 2 : ℝ) * ‖L ^ (1 / 2 : ℝ)‖ at hsmall
  change 2 ≤ y ∧ 0 < Real.log L ∧ Real.log L ≤ 4 * Real.log (y : ℝ) ∧ _
  have hLpos : 0 < L := by linarith
  have hlogpos : 0 < Real.log L := Real.log_pos (by linarith)
  have hytwo : 2 ≤ y := by
    apply Nat.le_floor
    push_cast
    exact Real.le_sqrt_of_sq_le (by norm_num; exact hfour)
  have hytwo' : (2 : ℝ) ≤ y := by exact_mod_cast hytwo
  have hyfloor : (y : ℝ) ≤ Real.sqrt L := Nat.floor_le (Real.sqrt_nonneg _)
  refine ⟨hytwo, hlogpos, ?_, ?_⟩
  · have hsqrt : Real.sqrt L ≤ (y : ℝ)^2 := by
      calc
        Real.sqrt L ≤ (y : ℝ) + 1 := (Nat.lt_floor_add_one _).le
        _ ≤ (y : ℝ)^2 := by nlinarith [sq_nonneg ((y : ℝ) - 2)]
    have h := Real.log_le_log (Real.sqrt_pos.2 hLpos) hsqrt
    rw [Real.log_sqrt hLpos.le, Real.log_pow] at h
    norm_num at h
    linarith
  · have harg : 0 < 1 + L / Real.log 2 := by positivity
    have hlogarg : 0 ≤ Real.log (1 + L / Real.log 2) :=
      Real.log_nonneg (by linarith [div_pos hLpos hlog2])
    have hargle : 1 + L / Real.log 2 ≤ L ^ 2 := by
      rw [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_left hlarge hLpos.le]
    have hlogle : Real.log (1 + L / Real.log 2) ≤ 2 * Real.log L := by
      simpa [Real.log_pow] using Real.log_le_log harg hargle
    rw [Real.rpow_two, ← Real.sqrt_eq_rpow, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hsmall
    apply (le_div_iff₀ hlogpos).2
    calc
      (y : ℝ) * Real.log (1 + L / Real.log 2) * Real.log L ≤
          Real.sqrt L * (2 * Real.log L) * Real.log L :=
        mul_le_mul_of_nonneg_right (mul_le_mul hyfloor hlogle hlogarg (Real.sqrt_nonneg _)) hlogpos.le
      _ = (2 * Real.sqrt L) * Real.log L ^ 2 := by ring
      _ ≤ (2 * Real.sqrt L) * ((1 / 2 : ℝ) * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = L := by
        convert Real.sq_sqrt hLpos.le using 1
        ring

private lemma factorization_le_log {a N : ℕ} (ha : 0 < a) (haN : a ≤ N) (p : ℕ) :
    a.factorization p ≤ Nat.log 2 N := by
  by_cases hp : p.Prime
  · apply Nat.le_log_of_pow_le (by decide)
    exact (Nat.pow_le_pow_left hp.two_le _).trans
      ((Nat.le_of_dvd ha (Nat.ordProj_dvd a p)).trans haN)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma smallExponentCount {A : Finset ℕ} {N y : ℕ} (hA : A ⊆ Finset.Icc 1 N) :
    (A.image (smallExponents y)).card ≤ (Nat.log 2 N + 1) ^ (y + 1) := by
  classical
  let I := A.image (smallExponents y)
  have hbound (u : I) (p : ℕ) : u.val p ≤ Nat.log 2 N := by
    obtain ⟨a, ha, hu⟩ := Finset.mem_image.mp u.property
    rw [← hu]
    have hmem := Finset.mem_Icc.mp (hA ha)
    by_cases hp : p ≤ y
    · simpa [smallExponents, Finsupp.filter_apply, hp] using
        factorization_le_log (by omega : 0 < a) hmem.2 p
    · simp [smallExponents, hp]
  let encode (u : I) (p : Fin (y + 1)) : Fin (Nat.log 2 N + 1) :=
    ⟨u.val p.val, Nat.lt_succ_of_le (hbound u _)⟩
  have hinj : Function.Injective encode := by
    intro u v h
    apply Subtype.ext
    ext p
    by_cases hp : p ≤ y
    · exact congrArg Fin.val (congrFun h ⟨p, Nat.lt_succ_of_le hp⟩)
    · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp u.property
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp v.property
      rw [← ha, ← hb]
      simp [smallExponents, hp]
  simpa [I, Fintype.card_fun] using Fintype.card_le_of_injective encode hinj

private lemma card_bound_from_fibers {A : Finset ℕ} {N y M : ℕ}
    (hA : A ⊆ Finset.Icc 1 N)
    (hfiber : ∀ u ∈ A.image (smallExponents y),
      (A.filter fun a => smallExponents y a = u).card ≤ M) :
    A.card ≤ (Nat.log 2 N + 1) ^ (y + 1) * M := by
  classical
  calc
    A.card = ∑ u ∈ A.image (smallExponents y),
        (A.filter fun a => smallExponents y a = u).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ _u ∈ A.image (smallExponents y), M := Finset.sum_le_sum hfiber
    _ = (A.image (smallExponents y)).card * M := by simp
    _ ≤ (Nat.log 2 N + 1) ^ (y + 1) * M := Nat.mul_le_mul_right _ (smallExponentCount hA)

private lemma f_le_of_card_le {r N M : ℕ} (hr : 0 < r)
    (h : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      (∀ S ⊆ A, S.card = r →
        ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) →
      A.card ≤ M) : f r N ≤ M := by
  apply csSup_le
  · refine ⟨0, ∅, Finset.empty_subset _, ?_, rfl⟩
    intro S hS hcard
    rw [Finset.subset_empty.mp hS, Finset.card_empty] at hcard
    omega
  rintro _ ⟨A, hA, hfree, rfl⟩
  exact h A hA hfree

private lemma cast_natLog_le {N b : ℕ} (hN : 0 < N) (hb : 1 < b) :
    (Nat.log b N : ℝ) ≤ log (N : ℝ) / log (b : ℝ) := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hpow : (b : ℝ) ^ Nat.log b N ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self b hN.ne'
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos hbR)).mpr hlog

private lemma bound_of_cutoff {N y B m : ℕ}
    (hN : 1 < N) (hy : 2 ≤ y) (hB : 1 ≤ B)
    (hloglog : 0 < log (log (N : ℝ)))
    (hylog : log (log (N : ℝ)) ≤ 4 * log (y : ℝ))
    (hsmall : (y : ℝ) * log (1 + log (N : ℝ) / log 2) ≤
      log (N : ℝ) / log (log (N : ℝ)))
    (hm : m ≤ (Nat.log 2 N + 1) ^ (y + 1) * B ^ Nat.log y N) :
    (m : ℝ) ≤ (N : ℝ) ^ ((2 + 4 * log (B : ℝ)) / log (log (N : ℝ))) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hyr : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hlogN := Real.log_pos hNr
  have hlogB := Real.log_nonneg hBr
  have hsmallbase : (Nat.log 2 N : ℝ) + 1 ≤ 1 + log (N : ℝ) / log 2 := by
    have h := cast_natLog_le (Nat.zero_lt_of_lt hN) (show 1 < (2 : ℕ) by decide)
    norm_num at h
    linarith
  have hsmallbase_pos : 0 < (Nat.log 2 N : ℝ) + 1 := by positivity
  have hsmallbase_log_nonneg : 0 ≤ log ((Nat.log 2 N : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hsmallbound : ((y : ℝ) + 1) * log ((Nat.log 2 N : ℝ) + 1) ≤
      2 * (log (N : ℝ) / log (log (N : ℝ))) := by
    calc
      _ ≤ (2 * (y : ℝ)) * log ((Nat.log 2 N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hsmallbase_log_nonneg
      _ ≤ (2 * (y : ℝ)) * log (1 + log (N : ℝ) / log 2) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hsmallbase_pos hsmallbase) (by positivity)
      _ = 2 * ((y : ℝ) * log (1 + log (N : ℝ) / log 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by norm_num)
  have hroughrank : (Nat.log y N : ℝ) ≤ 4 * (log (N : ℝ) / log (log (N : ℝ))) := by
    apply (cast_natLog_le (Nat.zero_lt_of_lt hN) (by omega)).trans
    calc
      log (N : ℝ) / log (y : ℝ) =
          4 * (log (N : ℝ) / (4 * log (y : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hlogN.le hloglog hylog) (by norm_num)
  have hcast : (m : ℝ) ≤ ((Nat.log 2 N : ℝ) + 1) ^ (y + 1) * (B : ℝ) ^ Nat.log y N := by
    exact_mod_cast hm
  refine hcast.trans ((Real.le_rpow_iff_log_le (by positivity) (by positivity : 0 < (N : ℝ))).mpr ?_)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Nat.cast_add,
     Nat.cast_one]
  calc
    _ ≤ 2 * (log (N : ℝ) / log (log (N : ℝ))) +
        (4 * (log (N : ℝ) / log (log (N : ℝ)))) * log (B : ℝ) :=
      add_le_add hsmallbound (mul_le_mul_of_nonneg_right hroughrank hlogB)
    _ = _ := by ring

private theorem gcdFiber_card_le {r N y D : ℕ} {A : Finset ℕ} (hr : 3 ≤ r) (hy : 2 ≤ y)
    (hA : A ⊆ Finset.Icc 1 N)
    (hfree : ∀ S ⊆ A, S.card = r → ¬ ∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)
    (hbound : ∀ (k : ℕ) (F : Finset (Finset (ℕ × ℕ))),
      SunflowerFree r F → (∀ U ∈ F, U.card ≤ k) → F.card ≤ D ^ k)
    (u : ℕ →₀ ℕ) : (A.filter fun a => smallExponents y a = u).card ≤ D ^ Nat.log y N := by
  classical
  let V := A.filter fun a => smallExponents y a = u
  let encode := staircase ∘ roughExponents y
  have hVA : V ⊆ A := Finset.filter_subset _ _
  have hpos {a : ℕ} (ha : a ∈ V) : a ≠ 0 :=
    Nat.ne_of_gt (Finset.mem_Icc.mp (hA (hVA ha))).1
  have hsm {a : ℕ} (ha : a ∈ V) : smallExponents y a = u := (Finset.mem_filter.mp ha).2
  have hinj : Set.InjOn encode V := fun _ ha _ hb heq =>
    eq_of_split_eq (hpos ha) (hpos hb) ((hsm ha).trans (hsm hb).symm) (staircase_injective heq)
  have hVfree : SunflowerFree r (V.image encode) := by
    refine sunflowerFree_image (by omega) (fun S hS => hfree S (hS.trans hVA)) hinj ?_
    intro a ha b hb c hc d hd hEq
    exact gcd_eq_of_fiber_inter (hpos ha) (hpos hb) (hpos hc) (hpos hd)
      (hsm ha) (hsm hb) (hsm hc) (hsm hd) hEq
  rw [← Finset.card_image_of_injOn hinj]
  apply hbound (Nat.log y N) _ hVfree
  intro U hU
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hU
  apply Nat.le_log_of_pow_le hy
  exact (rough_height y a (hpos ha)).trans (Finset.mem_Icc.mp (hA (hVA ha))).2

theorem erdos_535 : ∀ r ≥ 3, ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (f r N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) := by
  intro r hr
  obtain ⟨D, hD, hbound⟩ := exists_maxRankSunflowerBound hr
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨2 + 4 * log (D : ℝ), by linarith [Real.log_nonneg hDr], ?_⟩
  filter_upwards [cutoff_estimates, eventually_ge_atTop (2 : ℕ)] with N hcut hN
  let y := ⌊Real.sqrt (Real.log (N : ℝ))⌋₊
  obtain ⟨hy, hloglog, hylog, hsmall⟩ := hcut
  apply bound_of_cutoff (y := y) (by omega) hy hD hloglog hylog hsmall
  apply f_le_of_card_le (by omega)
  intro A hA hfree
  exact card_bound_from_fibers hA (fun u _ => gcdFiber_card_le hr hy hA hfree hbound u)

end Erdos535
