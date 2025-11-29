import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Holder
import SardMoreira.ContDiff

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

namespace Asymptotics

/-- If `a ≤ b`, then `x^b = O(x^a)` as `x → 0`, `x ≥ 0`, unless `b = 0` and `a ≠ 0`. -/
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le {a b : ℝ} (h : a ≤ b) (himp : b = 0 → a = 0) :
    (· ^ b : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) :=
  .of_bound' <| mem_of_superset (Icc_mem_nhdsGE one_pos) fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg hx.1, abs_of_nonneg hx.1]
     using Real.rpow_le_rpow_of_exponent_ge_of_imp hx.1 hx.2 h fun _ ↦ himp

theorem IsBigO.id_rpow_of_le_one {a : ℝ} (ha : a ≤ 1) :
    (id : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) := by
  simpa using rpow_rpow_nhdsGE_zero_of_le ha (by simp)

end Asymptotics

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDeriv_apply_congr_order {k l : ℕ} (h : k = l) (f : E → F) (x : E) (m : Fin k → E) :
    iteratedFDeriv ℝ k f x m = iteratedFDeriv ℝ l f x (m ∘ Fin.cast h.symm) := by
  subst l
  simp

structure ContDiffMoreiraHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  contDiffAt : ContDiffAt ℝ k f a
  isBigO : (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

theorem ContDiffAt.contDiffMoreiraHolderAt {n : WithTop ℕ∞} {k : ℕ} {f : E → F} {a : E}
    (h : ContDiffAt ℝ n f a) (hk : k < n) (α : I) : ContDiffMoreiraHolderAt k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) <| tendsto_norm_sub_self_nhdsGE a

namespace ContDiffMoreiraHolderAt

theorem continuousAt {k : ℕ} {α : I} {f : E → F} {a : E} (h : ContDiffMoreiraHolderAt k α f a) :
    ContinuousAt f a :=
  h.contDiffAt.continuousAt

theorem differentiableAt {k : ℕ} {α : I} {f : E → F} {a : E} (h : ContDiffMoreiraHolderAt k α f a)
    (hk : k ≠ 0) : DifferentiableAt ℝ f a :=
  h.contDiffAt.differentiableAt <| by norm_cast; omega

@[simp]
theorem zero_exponent_iff {k : ℕ} {f : E → F} {a : E} :
    ContDiffMoreiraHolderAt k 0 f a ↔ ContDiffAt ℝ k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

theorem of_exponent_le {k : ℕ} {f : E → F} {a : E} {α β : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hle : β ≤ α) : ContDiffMoreiraHolderAt k β f a where
  contDiffAt := hf.contDiffAt
  isBigO := hf.isBigO.trans <| by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le hle fun hα ↦ ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a

theorem of_lt {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hlt : l < k) : ContDiffMoreiraHolderAt l β f a :=
  hf.contDiffAt.contDiffMoreiraHolderAt (mod_cast hlt) _

theorem of_toLex_le {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hle : toLex (l, β) ≤ toLex (k, α)) : ContDiffMoreiraHolderAt l β f a :=
  (Prod.Lex.le_iff.mp hle).elim hf.of_lt <| by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

theorem of_le {k l : ℕ} {f : E → F} {a : E} {α : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hl : l ≤ k) : ContDiffMoreiraHolderAt l α f a :=
  hf.of_toLex_le <| Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

theorem of_contDiffOn_holderWith {f : E → F} {s : Set E} {k : ℕ} {α : I} {a : E} {C : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv ℝ k f) s) :
    ContDiffMoreiraHolderAt k α f a where
  contDiffAt := hf.contDiffAt hs
  isBigO := .of_bound C <| mem_of_superset hs fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using hd.dist_le hx (mem_of_mem_nhds hs)

theorem fst {k : ℕ} {α : I} {a : E × F} : ContDiffMoreiraHolderAt k α Prod.fst a :=
  contDiffAt_fst.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

theorem prodMk {k : ℕ} {α : I} {f : E → F} {g : E → G} {a : E}
    (hf : ContDiffMoreiraHolderAt k α f a) (hg : ContDiffMoreiraHolderAt k α g a) :
    ContDiffMoreiraHolderAt k α (fun x ↦ (f x, g x)) a where
  contDiffAt := hf.contDiffAt.prodMk hg.contDiffAt
  isBigO := calc
    _ =ᶠ[𝓝 a] (fun x ↦ (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f a).prod
                (iteratedFDeriv ℝ k g x - iteratedFDeriv ℝ k g a)) := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hg.contDiffAt.eventually (by simp)] with x hfx hgx
      apply DFunLike.ext
      rw [iteratedFDeriv_prodMk _ _ le_rfl, iteratedFDeriv_prodMk _ _ le_rfl] <;>
        simp [hfx, hgx, hf.contDiffAt, hg.contDiffAt]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      refine .of_norm_left ?_
      simp only [ContinuousMultilinearMap.opNorm_prod, ← Prod.norm_mk]
      exact (hf.isBigO.prod_left hg.isBigO).norm_left

theorem comp' {g : F → G} {f : E → F} {a : E} {k : ℕ} {α : I}
    (hg : ContDiffMoreiraHolderAt k α g (f a)) (hf : ContDiffMoreiraHolderAt k α f a)
    (hd : DifferentiableAt ℝ g (f a) ∨ DifferentiableAt ℝ f a) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a where
  contDiffAt := hg.contDiffAt.comp a hf.contDiffAt
  isBigO := calc
    (iteratedFDeriv ℝ k (g ∘ f) · - iteratedFDeriv ℝ k (g ∘ f) a)
      =ᶠ[𝓝 a] fun x ↦ (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) k -
        (ftaylorSeries ℝ g (f a)).taylorComp (ftaylorSeries ℝ f a) k := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hf.continuousAt.eventually (hg.contDiffAt.eventually (by simp))] with x hfx hgx
      rw [iteratedFDeriv_comp hgx hfx le_rfl,
        iteratedFDeriv_comp hg.contDiffAt hf.contDiffAt le_rfl]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
      · intro i hi
        exact ((hg.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).comp hf.continuousAt)
          |>.norm.isBoundedUnder_le
      · intro i hi
        by_cases hfd : DifferentiableAt ℝ f a
        · refine ((hg.of_le hi).isBigO.comp_tendsto hf.continuousAt).trans ?_
          refine .rpow α.2.1 (.of_forall fun _ ↦ norm_nonneg _) <| .norm_norm ?_
          exact hfd.isBigO_sub
        · obtain rfl : k = 0 := by
            contrapose! hfd
            exact hf.differentiableAt hfd
          obtain rfl : i = 0 := by rwa [nonpos_iff_eq_zero] at hi
          refine .of_norm_left ?_
          simp only [ftaylorSeries, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
            LinearIsometryEquiv.norm_map, isBigO_norm_left]
          refine ((hd.resolve_right hfd).isBigO_sub.comp_tendsto hf.continuousAt).trans ?_
          refine .trans (.of_norm_right ?_) hf.isBigO
          simp [iteratedFDeriv_zero_eq_comp, ← map_sub, Function.comp_def, isBigO_refl]
      · intro i hi
        exact (hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).norm.isBoundedUnder_le
      · exact fun _ _ ↦ isBoundedUnder_const
      · exact fun i hi ↦ (hf.of_le hi).isBigO

theorem comp {g : F → G} {f : E → F} {a : E} {k : ℕ} {α : I}
    (hg : ContDiffMoreiraHolderAt k α g (f a)) (hf : ContDiffMoreiraHolderAt k α f a)
    (hk : k ≠ 0) : ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  hg.comp' hf (.inl <| hg.differentiableAt hk)

theorem continuousLinearMap_comp {f : E → F} {a : E} {k : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (g : F →L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  g.contDiff.contDiffAt.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) _ |>.comp' hf <|
    .inl g.differentiableAt

@[simp]
theorem _root_.ContinuousLinearEquiv.contDiffMoreiraHolderAt_left_comp
    {f : E → F} {a : E} {k : ℕ} {α : I} (g : F ≃L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.continuousLinearMap_comp (g.symm : G →L[ℝ] F),
    fun h ↦ h.continuousLinearMap_comp (g : F →L[ℝ] G)⟩

@[simp]
theorem _root_.LinearIsometryEquiv.contDiffMoreiraHolderAt_left_comp
    {f : E → F} {a : E} {k : ℕ} {α : I} (g : F ≃ₗᵢ[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  g.toContinuousLinearEquiv.contDiffMoreiraHolderAt_left_comp

protected theorem fderiv {f : E → F} {a : E} {k l : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hl : l + 1 ≤ k) :
    ContDiffMoreiraHolderAt l α (fderiv ℝ f) a where
  contDiffAt := hf.contDiffAt.fderiv_right (mod_cast hl)
  isBigO := .of_norm_left <| by
    simpa [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, ← dist_eq_norm_sub]
      using hf.of_le hl |>.isBigO |>.norm_left

protected theorem iteratedFDeriv {f : E → F} {a : E} {k l m : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hl : l + m ≤ k) :
    ContDiffMoreiraHolderAt l α (iteratedFDeriv ℝ m f) a := by
  induction m generalizing l with
  | zero =>
    simpa +unfoldPartialApp [iteratedFDeriv_zero_eq_comp] using hf.of_le hl
  | succ m ihm =>
    rw [← add_assoc, add_right_comm] at hl
    -- TODO: why `simp` fails to apply the lemma? Does it fail to unify some instances?
    -- Does it happen on the latest Mathlib?
    simp +unfoldPartialApp [iteratedFDeriv_succ_eq_comp_left]
    convert (ihm hl).fderiv le_rfl using 0
    convert LinearIsometryEquiv.contDiffMoreiraHolderAt_left_comp _ <;> rfl

end ContDiffMoreiraHolderAt

structure ContDiffMoreiraHolderOn (k : ℕ) (α : I) (f : E → F) (s U : Set E) : Prop where
  subset : s ⊆ U
  isOpen : IsOpen U
  contDiffOn : ContDiffOn ℝ k f U
  isBigO : ∀ a ∈ s, (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

namespace ContDiffMoreiraHolderOn

variable {f : E → F} {s U : Set E} {k : ℕ} {α : I} {a : E}

theorem subset_left {t : Set E} (h : ContDiffMoreiraHolderOn k α f s U) (ht : t ⊆ s) :
    ContDiffMoreiraHolderOn k α f t U where
  __ := h
  subset := ht.trans h.subset
  isBigO a ha := h.isBigO a (ht ha)

theorem contDiffMoreiraHolderAt (h : ContDiffMoreiraHolderOn k α f s U) (ha : a ∈ s) :
    ContDiffMoreiraHolderAt k α f a :=
  ⟨h.contDiffOn.contDiffAt <| h.isOpen.mem_nhds <| h.subset ha, h.isBigO a ha⟩

theorem exists_superset :
    ∃ U, s ⊆ U ∧
      (ContDiffMoreiraHolderOn k α f s U ↔ ∀ x ∈ s, ContDiffMoreiraHolderAt k α f x) := by
  by_cases h : ∀ x ∈ s, ContDiffMoreiraHolderAt k α f x;
  · -- For each $x \in s$, there exists an open set $U_x$ containing $x$
    -- such that $f$ is $C^{k,\alpha}$ on $U_x$.
    have h_open : ∀ x ∈ s, ∃ U_x : Set E,
        IsOpen U_x ∧ x ∈ U_x ∧ ContDiffMoreiraHolderOn k α f {x} U_x := by
      intro x hx
      obtain ⟨U_x, hU_x_open, hxU_x, hU_x⟩ :
          ∃ U_x : Set E, IsOpen U_x ∧ x ∈ U_x ∧ ContDiffOn ℝ k f U_x ∧
            (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f x) =O[𝓝 x] (‖· - x‖ ^ (α : ℝ)) := by
        obtain ⟨U_x, hU_x_open, hxU_x, hU_x⟩ :
            ∃ U_x : Set E, IsOpen U_x ∧ x ∈ U_x ∧ ContDiffOn ℝ k f U_x := by
          -- By definition of ContDiffAt, there exists an open neighborhood U_x of x where f is C^k.
          obtain ⟨U_x, hU_x_open, hxU_x, hU_x_cont⟩ :
              ∃ U_x : Set E, IsOpen U_x ∧ x ∈ U_x ∧ ContDiffOn ℝ k f U_x := by
            have h_cont_diff : ContDiffAt ℝ k f x := by
              exact h x hx |>.1
            have := h_cont_diff.eventually;
            rcases mem_nhds_iff.mp (this (by norm_num)) with ⟨U, hU, hxU, hU'⟩;
            exact ⟨U, hxU, hU', fun y hy => hU hy |> ContDiffAt.contDiffWithinAt⟩;
          use U_x;
        exact ⟨U_x, hU_x_open, hxU_x, hU_x, h x hx |>.2⟩;
      use U_x;
      exact ⟨hU_x_open, hxU_x, ⟨by simpa, hU_x_open, hU_x.1, by simpa using hU_x.2⟩⟩;
    choose! U hU using h_open;
    refine ⟨⋃ x ∈ s, U x, ?_⟩;
    simp_all only [implies_true, iff_true]
    obtain ⟨val, property⟩ := α
    apply And.intro
    · exact fun x hx => Set.mem_iUnion₂.2 ⟨x, hx, hU x hx |>.2.1⟩;
    · constructor;
      · exact fun x hx => Set.mem_iUnion₂.2 ⟨x, hx, hU x hx |>.2.1⟩;
      · exact isOpen_biUnion fun x hx => hU x hx |>.1;
      · intro x hx;
        obtain ⟨y, hy, hy'⟩ := Set.mem_iUnion₂.mp hx;
        have := hU y hy;
        exact this.2.2.contDiffOn.contDiffAt (this.1.mem_nhds hy') |> ContDiffAt.contDiffWithinAt;
      · intro x hx;
        have := hU x hx |>.2.2.isBigO;
        exact this x rfl;
  · use univ; aesop (add unsafe ContDiffMoreiraHolderOn.contDiffMoreiraHolderAt)

theorem fst {s U : Set (E × F)} (hsub : s ⊆ U) (ho : IsOpen U) :
    ContDiffMoreiraHolderOn k α Prod.fst s U :=
  ⟨hsub, ho, contDiffOn_fst, fun _ _ ↦ ContDiffMoreiraHolderAt.fst.isBigO⟩

theorem prodMk {g : E → G} (hf : ContDiffMoreiraHolderOn k α f s U)
    (hg : ContDiffMoreiraHolderOn k α g s U) :
    ContDiffMoreiraHolderOn k α (fun x ↦ (f x, g x)) s U where
  __ := hf
  contDiffOn := hf.contDiffOn.prodMk hg.contDiffOn
  isBigO _a ha := ((hf.contDiffMoreiraHolderAt ha).prodMk (hg.contDiffMoreiraHolderAt ha)).isBigO

theorem _root_.ContDiffOn.contDiffMoreiraHolderOn {n : WithTop ℕ∞} (h : ContDiffOn ℝ n f U)
    (hs : s ⊆ U) (hU : IsOpen U) (hk : k < n) (α : I) : ContDiffMoreiraHolderOn k α f s U where
  subset := hs
  isOpen := hU
  contDiffOn := h.of_le hk.le
  isBigO _a ha := ((h.contDiffAt <| hU.mem_nhds <| hs ha).contDiffMoreiraHolderAt hk _).isBigO

theorem of_toLex_le (h : ContDiffMoreiraHolderOn k α f s U) {l β}
    (hl : toLex (l, β) ≤ toLex (k, α)) :
    ContDiffMoreiraHolderOn l β f s U where
  __ := h
  contDiffOn := h.contDiffOn.of_le <| mod_cast Prod.Lex.monotone_fst_ofLex hl
  isBigO _a ha := ((h.contDiffMoreiraHolderAt ha).of_toLex_le hl).isBigO

theorem of_lt (h : ContDiffMoreiraHolderOn k α f s U) {l β} (hl : l < k) :
    ContDiffMoreiraHolderOn l β f s U :=
  h.of_toLex_le <| .left _ _ hl

theorem of_le (h : ContDiffMoreiraHolderOn k α f s U) {l} (hl : l ≤ k) :
    ContDiffMoreiraHolderOn l α f s U :=
  h.of_toLex_le <| Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

theorem comp' {g : F → G} {t V : Set F} (hg : ContDiffMoreiraHolderOn k α g t V)
    (hf : ContDiffMoreiraHolderOn k α f s U) (hUV : MapsTo f U V) (hst : MapsTo f s t)
    (hd : DifferentiableOn ℝ g V ∨ DifferentiableOn ℝ f U) :
    ContDiffMoreiraHolderOn k α (g ∘ f) s U where
  __ := hf
  contDiffOn := hg.contDiffOn.comp hf.contDiffOn hUV
  isBigO _a ha :=
    ContDiffMoreiraHolderAt.isBigO <|
      (hg.contDiffMoreiraHolderAt <| hst ha).comp' (hf.contDiffMoreiraHolderAt ha) <|
        hd.imp (·.differentiableAt <| hg.isOpen.mem_nhds <| hUV <| hf.subset ha)
          (·.differentiableAt <| hf.isOpen.mem_nhds <| hf.subset ha)

theorem comp {g : F → G} {t V : Set F} (hg : ContDiffMoreiraHolderOn k α g t V)
    (hf : ContDiffMoreiraHolderOn k α f s U) (hUV : MapsTo f U V) (hst : MapsTo f s t)
    (hk : k ≠ 0) : ContDiffMoreiraHolderOn k α (g ∘ f) s U :=
  hg.comp' hf hUV hst <| .inl <| hg.contDiffOn.differentiableOn <| by simpa [Nat.one_le_iff_ne_zero]

theorem continuousLinearMap_comp (hf : ContDiffMoreiraHolderOn k α f s U) (g : F →L[ℝ] G) :
    ContDiffMoreiraHolderOn k α (g ∘ f) s U where
  __ := hf
  contDiffOn := g.contDiff.comp_contDiffOn hf.contDiffOn
  isBigO _a ha := ((hf.contDiffMoreiraHolderAt ha).continuousLinearMap_comp g).isBigO

end ContDiffMoreiraHolderOn
