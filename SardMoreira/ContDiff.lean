import Mathlib

open scoped unitInterval Topology NNReal Classical
open Function Asymptotics Filter Set

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E → F} {s : Set E}

section NWithTopENat
variable {n : WithTop ℕ∞} {k : ℕ} {a : E}

protected alias UniqueDiffOn.univ := uniqueDiffOn_univ

theorem ContinuousLinearMap.IsInvertible.eventually [CompleteSpace E] {α : Type*} {l : Filter α}
    {f₀ : E →L[𝕜] F} {f : α → E →L[𝕜] F} (hf₀ : f₀.IsInvertible) (hf : Tendsto f l (𝓝 f₀)) :
    ∀ᶠ x in l, (f x).IsInvertible :=
  hf.eventually <| ContinuousLinearEquiv.isOpen.mem_nhds hf₀

@[simp]
theorem ContinuousLinearMap.IsInvertible.self_comp_inverse {f : E →L[𝕜] F} (hf : f.IsInvertible) :
    f ∘L f.inverse = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
theorem ContinuousLinearMap.IsInvertible.inverse_comp_self {f : E →L[𝕜] F} (hf : f.IsInvertible) :
    f.inverse ∘L f = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

theorem ContinuousLinearMap.IsInvertible.bijective_inverse {f : E →L[𝕜] F} (hf : f.IsInvertible) :
    Bijective f.inverse := by
  rcases hf with ⟨e, rfl⟩
  simp [ContinuousLinearEquiv.bijective]

theorem ContinuousLinearMap.IsInvertible.injective_inverse {f : E →L[𝕜] F} (hf : f.IsInvertible) :
    Injective f.inverse :=
  hf.bijective_inverse.injective

theorem ContinuousLinearMap.isBigO_inverse_sub_inverse
    {α : Type*} {l : Filter α} {f g : α → E →L[𝕜] F}
    (hf_inv : ∀ᶠ a in l, (f a).IsInvertible)
    (hf_bdd : IsBoundedUnder (· ≤ ·) l (fun a ↦ ‖(f a).inverse‖))
    (hg_inv : ∀ᶠ a in l, (g a).IsInvertible)
    (hg_bdd : IsBoundedUnder (· ≤ ·) l (fun a ↦ ‖(g a).inverse‖)) :
    (fun a ↦ (f a).inverse - (g a).inverse) =O[l] (fun a ↦ f a - g a) := calc
  _ =ᶠ[l] fun a ↦ (f a).inverse ∘L (g a - f a) ∘L (g a).inverse := by
    filter_upwards [hf_inv, hg_inv] with a hfa hga
    simp [hfa, hga, ← comp_assoc]
  _ =O[l] fun a ↦ ‖(f a).inverse‖ * ‖g a - f a‖ * ‖(g a).inverse‖ := .of_norm_le fun a ↦ by
    grw [opNorm_comp_le, opNorm_comp_le, mul_assoc]
  _ =O[l] (fun a ↦ f a - g a) := by
    simpa [norm_sub_rev] using (hf_bdd.isBigO_one ℝ).norm_left.mul
      (isBigO_refl (fun a ↦ ‖g a - f a‖) _) |>.mul (hg_bdd.isBigO_one ℝ).norm_left

theorem ContinuousLinearEquiv.isBigO_symm_sub_symm {α : Type*} {l : Filter α} {f g : α → E ≃L[𝕜] F}
    (hf : IsBoundedUnder (· ≤ ·) l fun a ↦ (‖((f a).symm : F →L[𝕜] E)‖))
    (hg : IsBoundedUnder (· ≤ ·) l fun a ↦ (‖((g a).symm : F →L[𝕜] E)‖)) :
    (fun a ↦ ((f a).symm - (g a).symm : F →L[𝕜] E)) =O[l] (fun a ↦ (f a - g a : E →L[𝕜] F)) := by
  simp only [← ContinuousLinearMap.inverse_equiv] at *
  simpa using ContinuousLinearMap.isBigO_inverse_sub_inverse (by simp) hf (by simp) hg

protected theorem UniqueDiffOn.frequently_smallSets {s : Set E} (hs : UniqueDiffOn 𝕜 s) (a : E) :
    ∃ᶠ t in (𝓝[s] a).smallSets, t ∈ 𝓝[s] a ∧ UniqueDiffOn 𝕜 t := by
  rw [(nhdsWithin_basis_open _ _).smallSets.frequently_iff]
  exact fun U ⟨haU, hUo⟩ ↦ ⟨s ∩ U, (inter_comm _ _).le,
    inter_mem_nhdsWithin _ (hUo.mem_nhds haU), hs.inter hUo⟩

theorem ContDiffOn.continuousAt_iteratedFDerivWithin (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (ha : s ∈ 𝓝 a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDerivWithin 𝕜 k f s) a :=
  (hf.continuousOn_iteratedFDerivWithin hk hs).continuousAt ha

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

theorem ContDiffAt.eventually_isInvertible_fderiv [CompleteSpace E] (hf : ContDiffAt 𝕜 n f a)
    (ha : (fderiv 𝕜 f a).IsInvertible) (hn : n ≠ 0) :
    ∀ᶠ x in 𝓝 a, (fderiv 𝕜 f x).IsInvertible := by
  apply ha.eventually
  exact hf.continuousAt_fderiv hn

end NWithTopENat

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

theorem compContinuousLinearMap_compAlongOrderedFinpartition_left
    {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (f : F [×c.length]→L[𝕜] G) (g : ∀ i, E [×c.partSize i]→L[𝕜] F) (h : H →L[𝕜] E) :
    (c.compAlongOrderedFinpartition f g).compContinuousLinearMap (fun _ ↦ h) =
      c.compAlongOrderedFinpartition f fun i ↦ (g i).compContinuousLinearMap fun _ ↦ h := by
  ext
  simp [applyOrderedFinpartition_apply, Function.comp_def]

variable
    {α : Type*} {l : Filter α} {p₁ p₂ : α → F [×c.length]→L[𝕜] G}
    {q₁ q₂ : α → ∀ m, E [×c.partSize m]→L[𝕜] F} {B : α → ℝ} {i : ℕ}

theorem compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
    (hp_bdd : l.IsBoundedUnder (· ≤ ·) (‖p₁ ·‖))
    (hpB : (fun x ↦ p₁ x - p₂ x) =O[l] B)
    (hq₁_bdd : ∀ m, l.IsBoundedUnder (· ≤ ·) (‖q₁ · m‖))
    (hq₂_bdd : ∀ m, l.IsBoundedUnder (· ≤ ·) (‖q₂ · m‖))
    (hqB : ∀ m, (fun x ↦ q₁ x m - q₂ x m) =O[l] B) :
    (fun x ↦ (c.compAlongOrderedFinpartition (p₁ x) fun m ↦ q₁ x m) -
        c.compAlongOrderedFinpartition (p₂ x) fun m ↦ q₂ x m) =O[l] B := by
  refine .trans (.of_norm_le fun _ ↦
    c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le ..) ?_
  refine .add ?_ ?_
  · simp only [← isBigO_one_iff ℝ, ← isBigO_pi] at *
    have H := ((hq₁_bdd.prod_left hq₂_bdd).norm_left.pow (c.length - 1)).mul hqB.norm_left
    simpa [mul_assoc] using hp_bdd.norm_left.mul <| H.const_mul_left c.length
  · have H₂ : ∀ i, (q₂ · i) =O[l] (1 : α → ℝ) := fun i ↦ (hq₂_bdd i).isBigO_one ℝ
    simpa using hpB.norm_left.mul <| .finsetProd fun i _ ↦ (H₂ i).norm_left

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

variable {n : WithTop ℕ∞}

@[simp]
theorem ftaylorSeries_id (x : E) : ftaylorSeries 𝕜 id x = .id 𝕜 E x := by
  unfold ftaylorSeries
  ext (_ | _ | n) v <;> simp [iteratedFDeriv_succ_apply_right, FormalMultilinearSeries.id]

theorem ContinuousLinearMap.IsInvertible.hasFDerivAt {f : E → F} {x : E}
    (h : (fderiv 𝕜 f x).IsInvertible) : HasFDerivAt f (h.choose : E →L[𝕜] F) x := by
  rw [h.choose_spec]
  exact differentiableAt_of_isInvertible_fderiv h |>.hasFDerivAt

theorem OpenPartialHomeomorph.hasFDerivAt_symm_inverse (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    HasFDerivAt f.symm (fderiv 𝕜 f (f.symm y)).inverse y := by
  rw [ContinuousLinearMap.inverse, dif_pos hf']
  exact hf'.hasFDerivAt.of_local_left_inverse (f.symm.continuousAt hy)
    <| f.eventually_right_inverse hy

theorem OpenPartialHomeomorph.fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    fderiv 𝕜 f.symm y = (fderiv 𝕜 f (f.symm y)).inverse :=
  f.hasFDerivAt_symm_inverse hy hf' |>.fderiv

theorem OpenPartialHomeomorph.bijective_fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    Bijective (fderiv 𝕜 f.symm y) := by
  rw [f.fderiv_symm hy hf']
  exact hf'.bijective_inverse

theorem OpenPartialHomeomorph.injective_fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    Injective (fderiv 𝕜 f.symm y) :=
  f.bijective_fderiv_symm hy hf' |>.injective

theorem OpenPartialHomeomorph.contDiffAt_symm' [CompleteSpace E] (f : OpenPartialHomeomorph E F)
    {a : F} (ha : a ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm a)).IsInvertible)
    (hf : ContDiffAt 𝕜 n f (f.symm a)) : ContDiffAt 𝕜 n f.symm a := by
  exact f.contDiffAt_symm ha hf'.hasFDerivAt hf

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

theorem OpenPartialHomeomorph.iteratedFDeriv_symm_eq_rec [CompleteSpace E]
    (f : OpenPartialHomeomorph E F) {y : F} (hy : y ∈ f.target) (hf : ContDiffAt 𝕜 n f (f.symm y))
    {i : ℕ} (hi : i ≤ n) (hf' : 0 < i → (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    iteratedFDeriv 𝕜 i f.symm y =
      (FormalMultilinearSeries.id 𝕜 E (f.symm y) i -
        ∑ c ≠ OrderedFinpartition.atomic i,
          c.compAlongOrderedFinpartition (iteratedFDeriv 𝕜 c.length f.symm y)
            (fun m ↦ iteratedFDeriv 𝕜 (c.partSize m) f (f.symm y))).compContinuousLinearMap
      fun _ ↦ fderiv 𝕜 f.symm y := by
  rcases i.eq_zero_or_pos with rfl | hi₀
  · ext
    simp
  · specialize hf' hi₀
    rcases hf' with ⟨f', hf'⟩
    replace hf' : HasFDerivAt f (f' : E →L[𝕜] F) (f.symm y) :=
      hf' ▸ (hf.of_le hi |>.differentiableAt <| mod_cast hi₀).hasFDerivAt
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
    simp only [← H₃, FormalMultilinearSeries.taylorComp,
      FormalMultilinearSeries.compAlongOrderedFinpartition]
    rw [Fintype.sum_eq_add_sum_compl (OrderedFinpartition.atomic i), Finset.compl_singleton]
    ext v
    simp +unfoldPartialApp [OrderedFinpartition.applyOrderedFinpartition, ftaylorSeries, hf'.fderiv,
      (f.hasFDerivAt_symm hy hf').fderiv, Function.comp_def]

theorem OpenPartialHomeomorph.iteratedFDeriv_symm_eq_taylorLeftInv [CompleteSpace E]
    (f : OpenPartialHomeomorph E F) {y : F} (hy : y ∈ f.target) (hf : ContDiffAt 𝕜 n f (f.symm y))
    {i : ℕ} (hi : i ≤ n) (hf' : 0 < i → (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    iteratedFDeriv 𝕜 i f.symm y =
      (ftaylorSeries 𝕜 f (f.symm y)).taylorLeftInv (f.symm y) i := by
  fun_induction FormalMultilinearSeries.taylorLeftInv with | case1 i ih => ?_
  have H (c : OrderedFinpartition i) :
      c ∈ Finset.univ.erase (OrderedFinpartition.atomic i) ↔ c.length < i := by
    simp [OrderedFinpartition.length_lt_iff]
  rw [f.iteratedFDeriv_symm_eq_rec hy hf hi hf', Finset.sum_subtype (F := inferInstance) _ H]
  congr 3 with c : 1
  rw [ih]
  · simp [ftaylorSeries]
  · exact le_trans (mod_cast c.2.le) hi
  · exact fun hc ↦ hf' <| hc.trans c.2
  · simp [ftaylorSeries, iteratedFDeriv_one_eq, f.fderiv_symm hy (hf' c.pos)]

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
  apply c.compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
  exacts [hp_bdd _ c.length_le, hpB _ c.length_le, fun _ ↦ hq₁_bdd _ (c.partSize_le _),
    fun _ ↦ hq₂_bdd _ (c.partSize_le _), fun _ ↦ hqB _ (c.partSize_le _)]

end FormalMultilinearSeries
