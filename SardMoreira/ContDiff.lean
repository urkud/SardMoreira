import Mathlib

open scoped unitInterval Topology NNReal Classical
open Function Asymptotics Filter Set

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E → F} {s : Set E} {n : WithTop ℕ∞} {k : ℕ} {a : E}

protected alias UniqueDiffOn.univ := uniqueDiffOn_univ

theorem ContinuousLinearEquiv.isBigO_symm_sub_symm {α : Type*} {l : Filter α} {f g : α → E ≃L[𝕜] F}
    (hf : (fun a ↦ (f a).symm : α → F →L[𝕜] E) =O[l] (fun _ ↦ (1 : ℝ)))
    (hg : (fun a ↦ (g a).symm : α → F →L[𝕜] E) =O[l] (fun _ ↦ (1 : ℝ))) :
    (fun a ↦ ((f a).symm - (g a).symm : F →L[𝕜] E)) =O[l] (fun a ↦ (f a - g a : E →L[𝕜] F)) := by
  rw [Asymptotics.isBigO_iff'] at *;
  -- Using the identity `A⁻¹ - B⁻¹ = A⁻¹(B - A)B⁻¹`, we can bound the difference of the inverses.
  have h_diff_inv : ∀ a, ‖((f a).symm : F →L[𝕜] E) - ((g a).symm : F →L[𝕜] E)‖ ≤ ‖((f a).symm : F →L[𝕜] E)‖ * ‖((g a) : E →L[𝕜] F) - ((f a) : E →L[𝕜] F)‖ * ‖((g a).symm : F →L[𝕜] E)‖ := by
    -- Using the identity `A⁻¹ - B⁻¹ = A⁻¹(B - A)B⁻¹`, we can bound the difference of the inverses by the product of the norms of the inverses and the difference of the maps.
    have h_diff_inv : ∀ a, ((f a).symm : F →L[𝕜] E) - ((g a).symm : F →L[𝕜] E) = ((f a).symm : F →L[𝕜] E) ∘L (((g a) : E →L[𝕜] F) - ((f a) : E →L[𝕜] F)) ∘L ((g a).symm : F →L[𝕜] E) := by
      -- By definition of composition of linear maps, we can expand the right-hand side.
      intro a
      ext x
      simp
    -- Substitute h_diff_inv into the goal.
    intro a
    rw [h_diff_inv a];
    simpa only [ mul_assoc ] using ContinuousLinearMap.opNorm_comp_le _ _ |> le_trans <| mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) <| norm_nonneg _;
  simp +zetaDelta at *;
  -- Using the constants from hf and hg, we can construct the constant c.
  obtain ⟨c1, hc1_pos, hc1⟩ := hf
  obtain ⟨c2, hc2_pos, hc2⟩ := hg
  use c1 * c2;
  refine' ⟨ mul_pos hc1_pos hc2_pos, _ ⟩;
  -- By combining the inequalities from h_diff_inv and the bounds from hc1 and hc2, we can conclude the proof.
  have h_combined : ∀ᶠ x in l, ‖((f x).symm : F →L[𝕜] E) - ((g x).symm : F →L[𝕜] E)‖ ≤ c1 * ‖((g x) : E →L[𝕜] F) - ((f x) : E →L[𝕜] F)‖ * c2 := by
    filter_upwards [ hc1, hc2 ] with x hx1 hx2 using le_trans (h_diff_inv x) (by gcongr);
  filter_upwards [ h_combined ] with x hx using by simpa only [ mul_assoc, mul_comm, mul_left_comm, norm_sub_rev ] using hx;

/-
If `f` and `g` are families of continuous linear equivalences such that both the maps and their inverses are bounded, then the difference of their inverses is `Θ` of the difference of the maps.
-/
theorem ContinuousLinearEquiv.isTheta_symm_sub_symm {α : Type*} {l : Filter α} {f g : α → E ≃L[𝕜] F}
    (hf_symm : (fun a ↦ (f a).symm : α → F →L[𝕜] E) =O[l] (fun _ ↦ (1 : ℝ)))
    (hg_symm : (fun a ↦ (g a).symm : α → F →L[𝕜] E) =O[l] (fun _ ↦ (1 : ℝ)))
    (hf : (fun a ↦ (f a).toContinuousLinearMap) =O[l] (fun _ ↦ (1 : ℝ)))
    (hg : (fun a ↦ (g a).toContinuousLinearMap) =O[l] (fun _ ↦ (1 : ℝ))) :
    (fun a ↦ (f a).symm.toContinuousLinearMap - (g a).symm.toContinuousLinearMap) =Θ[l]
      (fun a ↦ (f a).toContinuousLinearMap - (g a).toContinuousLinearMap) := by
  refine' ⟨ _, _ ⟩;
  · exact isBigO_symm_sub_symm hf_symm hg_symm
  · convert isBigO_symm_sub_symm (f := fun a => (f a).symm) (g := fun a => (g a).symm) _ _
      using 1 <;> aesop

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
  (hf.iteratedFDerivWithin_right hs (by rwa [zero_add]) ha).continuousWithinAt

theorem ContDiffAt.continuousAt_iteratedFDeriv (hf : ContDiffAt 𝕜 n f a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDeriv 𝕜 k f) a := by
  simp only [← continuousWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact hf.contDiffWithinAt.continuousWithinAt_iteratedFDerivWithin uniqueDiffOn_univ trivial hk

theorem ContDiffAt.continuousAt_fderiv (hf : ContDiffAt 𝕜 n f a) (hn : n ≠ 0) :
    ContinuousAt (fderiv 𝕜 f) a :=
  hf.fderiv_right (show 0 + 1 ≤ n by simpa [ENat.one_le_iff_ne_zero_withTop]) |>.continuousAt

theorem iteratedFDerivWithin_prodMk {f : E → F} {g : E → G} (hf : ContDiffWithinAt 𝕜 n f s a)
    (hg : ContDiffWithinAt 𝕜 n g s a) (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (fun x ↦ (f x, g x)) s a =
      (iteratedFDerivWithin 𝕜 i f s a).prod (iteratedFDerivWithin 𝕜 i g s a) := by
  ext
  · rw [← ContinuousLinearMap.iteratedFDerivWithin_comp_left _ (hf.prodMk hg) hs ha hi]
    simp [Function.comp_def]
  · rw [← ContinuousLinearMap.iteratedFDerivWithin_comp_left _ (hf.prodMk hg) hs ha hi]
    simp [Function.comp_def]

theorem iteratedFDeriv_prodMk {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f a)
    (hg : ContDiffAt 𝕜 n g a) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (fun x ↦ (f x, g x)) a =
      (iteratedFDeriv 𝕜 i f a).prod (iteratedFDeriv 𝕜 i g a) := by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_prodMk hf.contDiffWithinAt hg.contDiffWithinAt .univ (mem_univ _) hi

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

namespace OrderedFinpartition

variable {n : ℕ} (c : OrderedFinpartition n)

/-- Cover `[0, n)`, `n ≠ 0`, by a single subset. -/
@[simps -fullyApplied]
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
  cases c with
  | _ length partSize partSize_pos emb emb_strictMono parts_strictMono disjoint cover => ?_
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
  cases c with | _ length partSize partSize_pos emb emb_strictMono parts_strictMono disjoint cover
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

namespace FormalMultilinearSeries

noncomputable def taylorLeftInv (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    FormalMultilinearSeries 𝕜 F E := fun n ↦
  FormalMultilinearSeries.id 𝕜 E x n -
    ∑ c : {c : OrderedFinpartition n // c.length < n},
      c.val.compAlongOrderedFinpartition (taylorLeftInv p x c.val.length)
        (fun m ↦ p (c.val.partSize m)) |>.compContinuousLinearMap fun _ ↦
          continuousMultilinearCurryFin1 𝕜 E F (p 1) |>.inverse

@[simp]
theorem taylorLeftInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    p.taylorLeftInv x 0 = .uncurry0 𝕜 F x := by
  have : IsEmpty {c : OrderedFinpartition 0 // c.length < 0} := by constructor; simp
  rw [taylorLeftInv, Fintype.sum_empty]
  ext
  simp

end FormalMultilinearSeries

@[simp]
theorem ftaylorSeries_id (x : E) : ftaylorSeries 𝕜 id x = .id 𝕜 E x := by
  unfold ftaylorSeries
  ext (_ | _ | n) v <;> simp [iteratedFDeriv_succ_apply_right, FormalMultilinearSeries.id]

theorem OpenPartialHomeomorph.fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (f' : E ≃L[𝕜] F) (hf' : HasFDerivAt f (f' : E →L[𝕜] F) (f.symm y)) :
    fderiv 𝕜 f.symm y = f'.symm :=
  (hf'.of_local_left_inverse (f.symm.continuousAt hy) <| f.eventually_right_inverse hy).fderiv

-- TODO: add before `HasFDerivAt.of_local_left_inverse`
theorem HasFDerivWithinAt.of_local_leftInverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    {s : Set E} {t : Set F} (hg : Tendsto g (𝓝[t] a) (𝓝[s] (g a)))
    (hf : HasFDerivWithinAt f (f' : E →L[𝕜] F) s (g a)) (ha : a ∈ t)
    (hfg : ∀ᶠ y in 𝓝[t] a, f (g y) = y) :
    HasFDerivWithinAt g (f'.symm : F →L[𝕜] E) t a := by
  have : (fun x : F => g x - g a - f'.symm (x - a)) =O[𝓝[t] a]
      fun x : F => f' (g x - g a) - (x - a) := by
    refine ((f'.symm : F →L[𝕜] E).isBigO_comp _ _).congr (fun x => ?_) fun _ => rfl
    simp
  refine .of_isLittleO <| this.trans_isLittleO ?_
  clear this
  refine ((hf.isLittleO.comp_tendsto hg).symm.congr' (hfg.mono ?_) .rfl).trans_isBigO ?_
  · intro p hp
    simp [hp, hfg.self_of_nhdsWithin ha]
  · refine ((hf.isBigO_sub_rev f'.antilipschitz).comp_tendsto hg).congr'
      (Eventually.of_forall fun _ => rfl) (hfg.mono ?_)
    rintro p hp
    simp only [(· ∘ ·), hp, hfg.self_of_nhdsWithin ha]

theorem iteratedFDeriv_one_eq (f : E → F) (x : E) :
    iteratedFDeriv 𝕜 1 f x = (continuousMultilinearCurryFin1 𝕜 E F).symm (fderiv 𝕜 f x) := by
  ext; simp

theorem OpenPartialHomeomorph.iteratedFDeriv_symm_eq_taylorLeftInv [CompleteSpace E]
    (f : OpenPartialHomeomorph E F) {y : F} (hy : y ∈ f.target) (hf : ContDiffAt 𝕜 n f (f.symm y))
    {i : ℕ} (hi : i ≤ n) (hf' : 0 < i → (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    iteratedFDeriv 𝕜 i f.symm y =
      (ftaylorSeries 𝕜 f (f.symm y)).taylorLeftInv (f.symm y) i := by
  rcases i.eq_zero_or_pos with rfl | hi₀
  · ext; simp
  · specialize hf' hi₀
    rcases hf' with ⟨f', hf'⟩
    replace hf' : HasFDerivAt f (f' : E →L[𝕜] F) (f.symm y) :=
      hf' ▸ (hf.of_le hi |>.differentiableAt <| mod_cast hi₀).hasFDerivAt
    fun_induction FormalMultilinearSeries.taylorLeftInv with | case1 i ih => ?_
    have H₁ : f.source ∈ 𝓝 (f.symm y) := f.open_source.mem_nhds <| f.symm_mapsTo hy
    have H₂ : ContDiffAt 𝕜 n f.symm (f (f.symm y)) := by
      rw [f.rightInvOn hy]
      exact f.contDiffAt_symm hy hf' hf
    have H₃ := calc
      (ftaylorSeries 𝕜 f.symm y).taylorComp (ftaylorSeries 𝕜 f (f.symm y)) i
      _ =  iteratedFDeriv 𝕜 i (f.symm ∘ f) (f.symm y) := by
        rw [iteratedFDeriv_comp H₂ hf hi, f.rightInvOn hy]
      _ = iteratedFDeriv 𝕜 i id (f.symm y) := by
        refine (EventuallyEq.iteratedFDeriv _ ?_ _).self_of_nhds
        filter_upwards [H₁] using f.leftInvOn
      _ = FormalMultilinearSeries.id 𝕜 E (f.symm y) i := by
        rw [← ftaylorSeries_id, ftaylorSeries]
    conv_rhs =>
      congr; congr; rfl; congr; rfl; intro c; congr
      exact (ih c (le_trans (mod_cast le_of_lt c.2) hi) (by simpa)).symm
    simp only [← H₃, FormalMultilinearSeries.taylorComp,
      FormalMultilinearSeries.compAlongOrderedFinpartition]
    have H₄ (c : OrderedFinpartition i) :
        c ∈ ({OrderedFinpartition.atomic i}ᶜ : Finset (OrderedFinpartition i)) ↔ c.length < i := by
      simp [OrderedFinpartition.length_lt_iff]
    rw [Fintype.sum_eq_add_sum_compl (OrderedFinpartition.atomic i),
      Finset.sum_subtype (F := inferInstance) _ H₄]
    ext v
    simp +unfoldPartialApp [OrderedFinpartition.applyOrderedFinpartition, ftaylorSeries, hf'.fderiv,
      Function.comp_def, iteratedFDeriv_one_eq]

namespace FormalMultilinearSeries

variable
    {α : Type*} {l : Filter α} {p₁ p₂ : α → FormalMultilinearSeries 𝕜 F G}
    {q₁ q₂ : α → FormalMultilinearSeries 𝕜 E F} {B : α → ℝ} {i n : ℕ}

theorem compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
    (hp_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖p₁ · k‖))
    (hpB : ∀ k ≤ n, (fun x ↦ p₁ x k - p₂ x k) =O[l] B)
    (hq₁_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₁ · k‖))
    (hq₂_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₂ · k‖))
    (hqB : ∀ k ≤ n, (fun x ↦ q₁ x k - q₂ x k) =O[l] B)
    (c : OrderedFinpartition n) :
    (fun x ↦ (p₁ x).compAlongOrderedFinpartition (q₁ x) c -
      (p₂ x).compAlongOrderedFinpartition (q₂ x) c) =O[l] B := by
  refine .trans (.of_norm_le fun _ ↦
    c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le ..) ?_
  refine .add ?_ ?_
  · have H₁ : (p₁ · c.length) =O[l] (1 : α → ℝ) := (hp_bdd _ c.length_le).isBigO_one ℝ
    have H₂ : ∀ m, (q₁ · (c.partSize m)) =O[l] (1 : α → ℝ) := fun m ↦
      (hq₁_bdd _ <| c.partSize_le _).isBigO_one ℝ
    have H₃ : ∀ m, (q₂ · (c.partSize m)) =O[l] (1 : α → ℝ) := fun m ↦
      (hq₂_bdd _ <| c.partSize_le _).isBigO_one ℝ
    have H₄ : ∀ m, (fun x ↦ q₁ x (c.partSize m) - q₂ x (c.partSize m)) =O[l] B := fun m ↦
      hqB _ <| c.partSize_le _
    rw [← isBigO_pi] at H₂ H₃ H₄
    have H₅ := ((H₂.prod_left H₃).norm_left.pow (c.length - 1)).mul H₄.norm_left
    simpa [mul_assoc] using H₁.norm_left.mul <| H₅.const_mul_left c.length
  · have H₁ : (fun x ↦ p₁ x c.length - p₂ x c.length) =O[l] B := hpB _ c.length_le
    have H₂ : ∀ i, (q₂ · (c.partSize i)) =O[l] (1 : α → ℝ) := fun i ↦
      (hq₂_bdd _ <| c.partSize_le i).isBigO_one ℝ
    simpa using H₁.norm_left.mul <| .finsetProd fun i _ ↦ (H₂ i).norm_left

theorem taylorComp_sub_taylorComp_isBigO
    (hp_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖p₁ · k‖))
    (hpB : ∀ k ≤ n, (fun x ↦ p₁ x k - p₂ x k) =O[l] B)
    (hq₁_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₁ · k‖))
    (hq₂_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₂ · k‖))
    (hqB : ∀ k ≤ n, (fun x ↦ q₁ x k - q₂ x k) =O[l] B) :
    (fun x ↦ (p₁ x).taylorComp (q₁ x) n - (p₂ x).taylorComp (q₂ x) n) =O[l] B := by
  simp only [FormalMultilinearSeries.taylorComp, ← Finset.sum_sub_distrib]
  refine .sum fun c _ ↦ ?_
  apply compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO <;> assumption

end FormalMultilinearSeries
