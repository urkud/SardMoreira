import Mathlib
import SardMoreira.ContDiff

open scoped Topology
open Filter Set

-- TODO: add before `HasFDerivAt.of_local_left_inverse`
theorem HasFDerivWithinAt.of_local_leftInverse {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
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

@[simps! -fullyApplied apply_coe symm_apply_coe_coe]
def Submodule.continuousEquivSubtypeMap {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] (p : Submodule R M) (q : Submodule R p) :
    q ≃L[R] q.map p.subtype where
  toLinearEquiv := p.equivSubtypeMap q
  continuous_toFun := .codRestrict (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := .codRestrict (.codRestrict continuous_subtype_val _) _

@[simps!]
def Submodule.topContinuousEquiv {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] :
    (⊤ : Submodule R M) ≃L[R] M where
  toLinearEquiv := topEquiv
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem ContinuousLinearEquiv.map_nhdsWithin_eq {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (e : M ≃L[R] N) (s : Set M) (x : M) :
    (𝓝[s] x).map e = 𝓝[e '' s] (e x) :=
  e.toHomeomorph.isInducing.map_nhdsWithin_eq _ _

theorem ContinuousLinearEquiv.map_nhdsWithin_preimage_eq {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (e : M ≃L[R] N) (s : Set N) (x : M) :
    (𝓝[e ⁻¹' s] x).map e = 𝓝[s] (e x) := by
  rw [e.map_nhdsWithin_eq, e.surjective.image_preimage]

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

def prodEquiv
    (s : Submodule R M) (t : Submodule R N) : s.prod t ≃ₗ[R] s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

@[simp]
theorem rank_prod_eq_lift [StrongRankCondition R] (s : Submodule R M) (t : Submodule R N)
    [Module.Free R s] [Module.Free R t] :
    Module.rank R (s.prod t) = (Module.rank R s).lift + (Module.rank R t).lift := by
  simp [(s.prodEquiv t).rank_eq]

@[simp]
theorem finrank_prod [StrongRankCondition R] (s : Submodule R M) (t : Submodule R N)
    [Module.Free R s] [Module.Free R t] [Module.Finite R s] [Module.Finite R t] :
    Module.finrank R (s.prod t) = Module.finrank R s + Module.finrank R t := by
  simp [(s.prodEquiv t).finrank_eq]

end Submodule

section ContDiff

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {n : WithTop ℕ∞} {k : ℕ} {a : E}

protected theorem UniqueDiffOn.frequently_smallSets {s : Set E} (hs : UniqueDiffOn 𝕜 s) (a : E) :
    ∃ᶠ t in (𝓝[s] a).smallSets, t ∈ 𝓝[s] a ∧ UniqueDiffOn 𝕜 t := by
  rw [(nhdsWithin_basis_open _ _).smallSets.frequently_iff]
  exact fun U ⟨haU, hUo⟩ ↦ ⟨s ∩ U, (inter_comm _ _).le,
    inter_mem_nhdsWithin _ (hUo.mem_nhds haU), hs.inter hUo⟩

theorem iteratedFDeriv_apply_congr_order
    {k l : ℕ} (h : k = l) (f : E → F) (x : E) (m : Fin k → E) :
    iteratedFDeriv 𝕜 k f x m = iteratedFDeriv 𝕜 l f x (m ∘ Fin.cast h.symm) := by
  subst l
  simp

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

end ContDiff

namespace OrderedFinpartition

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

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

end OrderedFinpartition
