import Mathlib.Analysis.Calculus.ContDiff.Basic
import SardMoreira.ContinuousMultilinearMap

open scoped unitInterval Topology NNReal
open Function Asymptotics Filter Set

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E → F} {s : Set E} {n : WithTop ℕ∞} {k : ℕ} {a : E}

protected alias UniqueDiffOn.univ := uniqueDiffOn_univ

theorem Asymptotics.IsBigO.of_norm_eventuallyLE {α : Type*} {l : Filter α} {f : α → E}
    {g : α → ℝ} (h : (‖f ·‖) ≤ᶠ[l] g) : f =O[l] g :=
  .of_bound' <| h.mono fun _ h ↦ h.trans <| le_abs_self _

theorem Asymptotics.IsBigO.of_norm_le {α : Type*} {l : Filter α} {f : α → E}
    {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : f =O[l] g :=
  .of_norm_eventuallyLE <| .of_forall h

theorem Asymptotics.IsBigO.finsetProd {α ι R K : Type*} [SeminormedCommRing R] [NormedField K]
    {l : Filter α} {s : Finset ι} {f : ι → α → R} {g : ι → α → K}
    (hf : ∀ i ∈ s, f i =O[l] g i) : (∏ i ∈ s, f i ·) =O[l] (∏ i ∈ s, g i ·) := by
  induction s using Finset.cons_induction with
  | empty => simp [isBoundedUnder_const]
  | cons i s hi ihs =>
    simp only [Finset.prod_cons, Finset.forall_mem_cons] at hf ⊢
    exact hf.1.mul (ihs hf.2)

@[simp]
theorem Prod.norm_mk {E F : Type*} [Norm E] [Norm F] (a : E) (b : F) : ‖(a, b)‖ = max ‖a‖ ‖b‖ := rfl

protected theorem UniqueDiffOn.frequently_smallSets {s : Set E} (hs : UniqueDiffOn 𝕜 s) (a : E) :
    ∃ᶠ t in (𝓝[s] a).smallSets, t ∈ 𝓝[s] a ∧ UniqueDiffOn 𝕜 t := by
  rw [(nhdsWithin_basis_open _ _).smallSets.frequently_iff]
  exact fun U ⟨haU, hUo⟩ ↦ ⟨s ∩ U, (inter_comm _ _).le,
    inter_mem_nhdsWithin _ (hUo.mem_nhds haU), hs.inter hUo⟩

theorem ContDiffOn.continuousAt_iteratedFDerivWithin (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (ha : s ∈ 𝓝 a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDerivWithin 𝕜 k f s) a :=
  (hf.continuousOn_iteratedFDerivWithin hk hs).continuousAt ha

theorem ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin (hf : ContDiffWithinAt 𝕜 n f s a)
    (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) (hk : k ≤ n) :
    ContinuousWithinAt (iteratedFDerivWithin 𝕜 k f s) s a :=
  (hf.iteratedFderivWithin_right hs (by rwa [zero_add]) ha).continuousWithinAt

theorem ContDiffAt.continuousAt_iteratedFDeriv (hf : ContDiffAt 𝕜 n f a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDeriv 𝕜 k f) a := by
  simp only [← continuousWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact hf.contDiffWithinAt.continuousWithinAt_iteratedFDerivWithin uniqueDiffOn_univ trivial hk

theorem ContDiffAt.differentiableAt_iteratedFDeriv (hf : ContDiffAt 𝕜 n f a) (hk : k < n) :
    DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 k f) a := by
  simp only [← differentiableWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact hf.differentiableWithinAt_iteratedFDerivWithin hk (by simp [uniqueDiffOn_univ])

/-- Generalizes `ContinuousLinearMap.iteratedFderivWithin_comp_left`
by weakening a `ContDiffOn` assumption to `ContDiffWithinAt`.  -/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_left' (g : F →L[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s a) (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s a =
      g.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s a) := by
  rcases hf.contDiffOn' hi (by simp) with ⟨U, hU, haU, hfU⟩
  rw [← iteratedFDerivWithin_inter_open hU haU, ← iteratedFDerivWithin_inter_open (f := f) hU haU]
  rw [insert_eq_of_mem ha] at hfU
  exact .symm <| (hfU.ftaylorSeriesWithin (hs.inter hU)).continuousLinearMap_comp g
    |>.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter hU) ⟨ha, haU⟩

/-- Generalizes `ContinuousLinearMap.iteratedFderiv_comp_left`
by weakening a `ContDiff` assumption to `ContDiffAt`.  -/
theorem ContinuousLinearMap.iteratedFDeriv_comp_left' (g : F →L[𝕜] G) (hf : ContDiffAt 𝕜 n f a)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (g ∘ f) a = g.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f a) := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_left' hf.contDiffWithinAt .univ (mem_univ _) hi

theorem iteratedFDerivWithin_prodMk {f : E → F} {g : E → G} (hf : ContDiffWithinAt 𝕜 n f s a)
    (hg : ContDiffWithinAt 𝕜 n g s a) (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (fun x ↦ (f x, g x)) s a =
      (iteratedFDerivWithin 𝕜 i f s a).prod (iteratedFDerivWithin 𝕜 i g s a) := by
  rw [ContinuousMultilinearMap.eq_prod_iff,
    ← ContinuousLinearMap.iteratedFDerivWithin_comp_left' _ (hf.prod hg) hs ha hi,
    ← ContinuousLinearMap.iteratedFDerivWithin_comp_left' _ (hf.prod hg) hs ha hi]
  exact ⟨rfl, rfl⟩

theorem iteratedFDeriv_prodMk {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f a)
    (hg : ContDiffAt 𝕜 n g a) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (fun x ↦ (f x, g x)) a =
      (iteratedFDeriv 𝕜 i f a).prod (iteratedFDeriv 𝕜 i g a) := by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_prodMk hf.contDiffWithinAt hg.contDiffWithinAt .univ (mem_univ _) hi

theorem ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn {f : E → F} {s : Set E} {a : E}
    (h : ContDiffWithinAt 𝕜 n f s a) (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) {m : ℕ} (hm : m ≤ n) :
    ∀ᶠ t in (𝓝[s] a).smallSets, HasFTaylorSeriesUpToOn m f (ftaylorSeriesWithin 𝕜 f s) t := by
  rcases h.contDiffOn' hm (by simp) with ⟨U, hUo, haU, hfU⟩
  have : ∀ᶠ t in (𝓝[s] a).smallSets, t ⊆ s ∩ U := by
    rw [eventually_smallSets_subset]
    exact inter_mem_nhdsWithin _ <| hUo.mem_nhds haU
  refine this.mono fun t ht ↦ .mono ?_ ht
  rw [insert_eq_of_mem ha] at hfU
  refine (hfU.ftaylorSeriesWithin (hs.inter hUo)).congr_series fun k hk x hx ↦ ?_
  exact iteratedFDerivWithin_inter_open hUo hx.2

theorem iteratedFDerivWithin_comp_of_eventually
    {g : F → G} {f : E → F} {t : Set F} {s : Set E} {a : E}
    (hg : ContDiffWithinAt 𝕜 n g t (f a)) (hf : ContDiffWithinAt 𝕜 n f s a)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) (hst : ∀ᶠ x in 𝓝[s] a, f x ∈ t)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s a =
      (ftaylorSeriesWithin 𝕜 g t (f a)).taylorComp (ftaylorSeriesWithin 𝕜 f s a) i := by
  have hat : f a ∈ t := hst.self_of_nhdsWithin ha
  have hf_tendsto : Tendsto f (𝓝[s] a) (𝓝[t] (f a)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hf.continuousWithinAt, hst⟩
  have H₁ : ∀ᶠ u in (𝓝[s] a).smallSets, u ⊆ s :=
    eventually_smallSets_subset.mpr eventually_mem_nhdsWithin
  have H₂ : ∀ᶠ u in (𝓝[s] a).smallSets, HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) u :=
    hf.eventually_hasFTaylorSeriesUpToOn hs ha hi
  have H₃ := hf_tendsto.image_smallSets.eventually
    (hg.eventually_hasFTaylorSeriesUpToOn ht hat hi)
  rcases ((hs.frequently_smallSets _).and_eventually (H₁.and <| H₂.and H₃)).exists
    with ⟨u, ⟨hau, hu⟩, hus, hfu, hgu⟩
  refine .symm <| (hgu.comp hfu (mapsTo_image _ _)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
    hu (mem_of_mem_nhdsWithin ha hau) |>.trans ?_
  refine iteratedFDerivWithin_congr_set (hus.eventuallyLE.antisymm ?_) _
  exact set_eventuallyLE_iff_mem_inf_principal.mpr hau

theorem iteratedFDerivWithin_comp {g : F → G} {f : E → F} {t : Set F} {s : Set E} {a : E}
    (hg : ContDiffWithinAt 𝕜 n g t (f a)) (hf : ContDiffWithinAt 𝕜 n f s a)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) (hst : MapsTo f s t)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s a =
      (ftaylorSeriesWithin 𝕜 g t (f a)).taylorComp (ftaylorSeriesWithin 𝕜 f s a) i :=
  iteratedFDerivWithin_comp_of_eventually hg hf ht hs ha (eventually_mem_nhdsWithin.mono hst) hi

theorem iteratedFDeriv_comp {g : F → G} {f : E → F} {a : E} (hg : ContDiffAt 𝕜 n g (f a))
    (hf : ContDiffAt 𝕜 n f a) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (g ∘ f) a =
      (ftaylorSeries 𝕜 g (f a)).taylorComp (ftaylorSeries 𝕜 f a) i := by
  simp only [← iteratedFDerivWithin_univ, ← ftaylorSeriesWithin_univ]
  exact iteratedFDerivWithin_comp hg.contDiffWithinAt hf.contDiffWithinAt .univ .univ (mem_univ _)
    (mapsTo_univ _ _) hi

namespace OrderedFinpartition

variable {n : ℕ} (c : OrderedFinpartition n)

/-- Cover `[0, n)`, `n ≠ 0`, by a single subset. -/
@[simps (config := .asFn)]
def single (n : ℕ) (hn : n ≠ 0) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn.bot_lt
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := subsingleton_univ.pairwise _
  cover x := ⟨0, x, rfl⟩

@[simp]
theorem applyOrderedFinpartition_single (hn : n ≠ 0)
    (p : ∀ i : Fin (single n hn).length, E [×(single n hn).partSize i]→L[𝕜] F)
    (m : Fin n → E) (i : Fin (single n hn).length) :
    (single n hn).applyOrderedFinpartition p m i = p i m :=
  rfl

@[simp]
theorem sum_partSize : ∑ i, c.partSize i = n := calc
  ∑ i, c.partSize i = Fintype.card (Σ i, Fin (c.partSize i)) := by simp
  _ = n := by rw [Fintype.card_congr c.equivSigma, Fintype.card_fin]

@[simp]
theorem length_eq_zero : c.length = 0 ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ nonpos_iff_eq_zero.mp <| h ▸ c.length_le⟩
  rw [← c.sum_partSize, Finset.sum_eq_zero]
  simp [(c.partSize_pos _).ne', h]

@[simp] theorem length_pos_iff : 0 < c.length ↔ 0 < n := by simp [pos_iff_ne_zero]

theorem length_eq_one_iff (hn : n ≠ 0) : c.length = 1 ↔ c = single n hn := by
  refine ⟨fun hc ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hsum := c.sum_partSize
  cases' c with length partSize partSize_pos emb emb_strictMono parts_strictMono disjoint cover
  subst hc
  obtain rfl : partSize = fun _ ↦ n := by
    rw [funext_iff, Fin.forall_fin_one]
    simpa using hsum
  obtain rfl : emb = fun _ ↦ id := by
    rw [funext_iff, Fin.forall_fin_one, ← (emb_strictMono 0).range_inj strictMono_id]
    simpa [eq_univ_iff_forall, Fin.exists_fin_one] using cover
  rfl

theorem length_eq_one_iff_exists : c.length = 1 ↔ ∃ h, c = single n h := by
  refine ⟨fun hc ↦ ?_, fun ⟨_, h⟩ ↦ h ▸ rfl⟩
  suffices n ≠ 0 from ⟨this, (c.length_eq_one_iff this).mp hc⟩
  simp [← c.length_eq_zero, hc]

theorem partSize_eq_iff_length_eq_one (i : Fin c.length) : c.partSize i = n ↔ c.length = 1 := by
  constructor
  · intro h
    by_contra h'
    have : Nontrivial (Fin c.length) := by
      rw [Fin.nontrivial_iff_two_le]
      have := i.is_lt
      omega
    rcases exists_ne i with ⟨j, hj⟩
    refine h.not_lt <| LT.lt.trans_eq ?_ c.sum_partSize
    exact Finset.single_lt_sum hj (Finset.mem_univ _) (Finset.mem_univ _) (c.partSize_pos _)
      (by simp)
  · rw [length_eq_one_iff_exists]
    rintro ⟨h, rfl⟩
    rfl

theorem partSize_eq_iff_eq_single (i : Fin c.length) :
    c.partSize i = n ↔ c = single n (i.is_lt.trans_le c.length_le).ne_bot := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rwa [c.partSize_eq_iff_length_eq_one i, length_eq_one_iff] at h
  · generalize_proofs at h
    subst h
    rfl


theorem length_eq_iff : c.length = n ↔ c = atomic n := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have H₀ := c.sum_partSize
  cases' c with length partSize partSize_pos emb emb_strictMono parts_strictMono disjoint cover
  dsimp at *
  subst h
  obtain rfl : partSize = fun _ ↦ 1 := by
    suffices ∀ i ∈ Finset.univ, 1 = partSize i by simpa [eq_comm, funext_iff] using this
    rw [← Finset.sum_eq_sum_iff_of_le]
    · simp [H₀]
    · exact fun i _ ↦ partSize_pos i
  obtain rfl : emb = fun i _ ↦ i := by
    suffices ∀ i, emb i 0 = i by
      ext i j : 2
      convert this i
    rw [← funext_iff, ← StrictMono.range_inj, Surjective.range_eq, Surjective.range_eq]
    exacts [surjective_id, Finite.surjective_of_injective parts_strictMono.injective,
      parts_strictMono, strictMono_id]
  rfl

theorem length_lt_iff : c.length < n ↔ c ≠ atomic n := by
  rw [c.length_le.lt_iff_ne]
  exact c.length_eq_iff.not

theorem norm_compAlongOrderedFinpartitionL_apply_le (f : F [×c.length]→L[𝕜] G) :
    ‖c.compAlongOrderedFinpartitionL 𝕜 E F G f‖ ≤ ‖f‖ :=
  (ContinuousLinearMap.le_of_opNorm_le _ c.norm_compAlongOrderedFinpartitionL_le f).trans_eq
    (one_mul _)

theorem norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (f₁ f₂ : F [×c.length]→L[𝕜] G) (g₁ g₂ : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₂ g₂‖ ≤
      ‖f₁‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := calc
  _ ≤ ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₁ g₂‖ +
      ‖c.compAlongOrderedFinpartition f₁ g₂ - c.compAlongOrderedFinpartition f₂ g₂‖ :=
    norm_sub_le_norm_sub_add_norm_sub ..
  _ ≤ ‖f₁‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := by
    gcongr
    · refine ((c.compAlongOrderedFinpartitionL 𝕜 E F G f₁).norm_image_sub_le g₁ g₂).trans ?_
      simp only [Fintype.card_fin]
      gcongr
      apply norm_compAlongOrderedFinpartitionL_apply_le
    · exact c.norm_compAlongOrderedFinpartition_le (f₁ - f₂) g₂

end OrderedFinpartition

theorem FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
    {α : Type*} {l : Filter α} {p₁ p₂ : α → FormalMultilinearSeries 𝕜 F G}
    {q₁ q₂ : α → FormalMultilinearSeries 𝕜 E F} {f : α → ℝ} {n : ℕ}
    (hp_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖p₁ · k‖))
    (hpf : ∀ k ≤ n, (fun x ↦ p₁ x k - p₂ x k) =O[l] f)
    (hq₁_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₁ · k‖))
    (hq₂_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₂ · k‖))
    (hqf : ∀ k ≤ n, (fun x ↦ q₁ x k - q₂ x k) =O[l] f) :
    (fun x ↦ (p₁ x).taylorComp (q₁ x) n - (p₂ x).taylorComp (q₂ x) n) =O[l] f := by
  simp only [FormalMultilinearSeries.taylorComp, ← Finset.sum_sub_distrib]
  refine .sum fun c _ ↦ ?_
  refine .trans (.of_norm_le fun _ ↦
    c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le ..) ?_
  refine .add ?_ ?_
  · have H₁ : (p₁ · c.length) =O[l] (1 : α → ℝ) := (hp_bdd _ c.length_le).isBigO_one ℝ
    have H₂ : ∀ m, (q₁ · (c.partSize m)) =O[l] (1 : α → ℝ) := fun m ↦
      (hq₁_bdd _ <| c.partSize_le _).isBigO_one ℝ
    have H₃ : ∀ m, (q₂ · (c.partSize m)) =O[l] (1 : α → ℝ) := fun m ↦
      (hq₂_bdd _ <| c.partSize_le _).isBigO_one ℝ
    have H₄ : ∀ m, (fun x ↦ q₁ x (c.partSize m) - q₂ x (c.partSize m)) =O[l] f := fun m ↦
      hqf _ <| c.partSize_le _
    rw [← isBigO_pi] at H₂ H₃ H₄
    have H₅ := ((H₂.prod_left H₃).norm_left.pow (c.length - 1)).mul H₄.norm_left
    simpa [mul_assoc] using H₁.norm_left.mul <| H₅.const_mul_left c.length
  · have H₁ : (fun x ↦ p₁ x c.length - p₂ x c.length) =O[l] f := hpf _ c.length_le
    have H₂ : ∀ i, (q₂ · (c.partSize i)) =O[l] (1 : α → ℝ) := fun i ↦
      (hq₂_bdd _ <| c.partSize_le i).isBigO_one ℝ
    simpa using H₁.norm_left.mul <| .finsetProd fun i _ ↦ (H₂ i).norm_left
