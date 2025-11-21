import SardMoreira.ContDiffMoreiraHolder
import Mathlib

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set Metric Function

namespace MoreiraSard

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

structure Chart (k : ℕ) (α : I) (l : Fin (k + 1)) (s U : Set (E × F)) where
  subspace : Fin (l + 1) → Submodule ℝ F
  subspace_anti : Antitone subspace
  center : E × F
  radiusLeft : Fin (l + 1) → ℝ
  radiusLeft_anti : Antitone radiusLeft
  radiusLeft_pos i : 0 < radiusLeft i
  radiusRight : Fin (l + 1) → ℝ
  radiusRight_pos i : 0 < radiusRight i
  toFunSnd (i : Fin l) : E → subspace i.succ → subspace i.castSucc
  holderSet (i : Fin (l + 1)) : Set (E × subspace i)
  holderSet_subset_dom_zero : holderSet 0 ⊆ ball 0 (radiusLeft 0) ×ˢ ball 0 (radiusRight 0)
  mapsTo_holderSet_zero' : MapsTo (fun xy ↦ (xy.1, xy.2.1) + center) (holderSet 0) s
  mapsTo_dom_zero : MapsTo (fun xy ↦ (xy.1, xy.2.1) + center)
    (ball 0 (radiusLeft 0) ×ˢ ball (0 : subspace 0) (radiusRight 0)) U
  mapsTo_holderSet' (i : Fin l) :
    MapsTo (fun xy ↦ (xy.1, toFunSnd i xy.1 xy.2)) (holderSet i.succ) (holderSet i.castSucc)
  toFunSnd_mem_ball (i : Fin l) {x : E} {y : subspace i.succ} :
    x ∈ ball 0 (radiusLeft i.succ) → y ∈ ball 0 (radiusRight i.succ) →
      toFunSnd i x y ∈ ball 0 (radiusRight i.castSucc)
  contDiffMoreiraHolderOn_toFunSnd (i : Fin l) :
    ContDiffMoreiraHolderOn (k - i) α (toFunSnd i).uncurry (holderSet i.succ)
      (ball 0 (radiusLeft i.succ) ×ˢ ball 0 (radiusRight i.succ))
  dist_le_toFunSnd {i : Fin l} {x : E} {y₁ y₂ : subspace i.succ} :
    x ∈ ball 0 (radiusLeft i.succ) → y₁ ∈ ball 0 (radiusRight i.succ) →
      y₂ ∈ ball 0 (radiusRight i.succ) → dist y₁ y₂ ≤ dist (toFunSnd i x y₁) (toFunSnd i x y₂)
  fderiv_comp_eq_zero' (i : Fin l) (f : E → (subspace i.castSucc) → ℝ) :
    ContDiffMoreiraHolderOn (k - i) α f.uncurry (holderSet i.castSucc)
      (ball 0 (radiusLeft i.castSucc) ×ˢ ball 0 (radiusRight i.castSucc)) →
    (∀ p ∈ holderSet i.castSucc, f p.1 p.2 = 0) →
    ∀ x y, (x, y) ∈ holderSet i.succ → fderiv ℝ (f x ∘ toFunSnd i x) y = 0

namespace Chart

variable {k : ℕ} {l : Fin (k + 1)} {α : I} {s U : Set (E × F)}

@[coe]
def toFun (ψ : Chart k α l s U) (i : Fin l) :
    E × ψ.subspace i.succ → E × ψ.subspace i.castSucc :=
  fun xy ↦ (xy.1, ψ.toFunSnd i xy.1 xy.2)

instance instCoeFun : CoeFun (Chart k α l s U) fun ψ ↦ ∀ i : Fin l,
    E × ψ.subspace i.succ → E × ψ.subspace i.castSucc :=
  ⟨toFun⟩

theorem apply_fst (ψ : Chart k α l s U) (i : Fin l) (x : E × ψ.subspace i.succ) :
    (ψ i x).1 = x.1 :=
  rfl

/-- The product of balls where the map $\psi_i$ is $C^{k-i+(\alpha)}$. -/
def dom (ψ : Chart k α l s U) (i : Fin (l + 1)) : Set (E × ψ.subspace i) :=
  ball 0 (ψ.radiusLeft i) ×ˢ ball 0 (ψ.radiusRight i)

theorem isOpen_dom (ψ : Chart k α l s U) (i : Fin (l + 1)) : IsOpen (ψ.dom i) :=
  .prod isOpen_ball isOpen_ball

theorem dom_nonempty (ψ : Chart k α l s U) (i : Fin (l + 1)) : (ψ.dom i).Nonempty :=
  .prod (nonempty_ball.2 <| ψ.radiusLeft_pos i) (nonempty_ball.2 <| ψ.radiusRight_pos i)

theorem holderSet_subset_dom (ψ : Chart k α l s U) (i : Fin (l + 1)) :
    ψ.holderSet i ⊆ ψ.dom i := by
  induction i using Fin.cases with
  | zero => exact ψ.holderSet_subset_dom_zero
  | succ i => exact (ψ.contDiffMoreiraHolderOn_toFunSnd i).subset

theorem mapsTo_dom (ψ : Chart k α l s U) (i : Fin l) :
    MapsTo (ψ i) (ψ.dom i.succ) (ψ.dom i.castSucc) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨ball_subset_ball (ψ.radiusLeft_anti i.castSucc_le_succ) hx, ψ.toFunSnd_mem_ball i hx hy⟩

theorem mapsTo_holderSet (ψ : Chart k α l s U) (i : Fin l) :
    MapsTo (ψ i) (ψ.holderSet i.succ) (ψ.holderSet i.castSucc) :=
  ψ.mapsTo_holderSet' i

theorem contDiffMoreiraHolderOn (ψ : Chart k α l s U) (i : Fin l) :
    ContDiffMoreiraHolderOn (k - i) α (ψ i) (ψ.holderSet i.succ) (ψ.dom i.succ) :=
  .prodMk (.fst (ψ.holderSet_subset_dom _) (ψ.isOpen_dom _)) (ψ.contDiffMoreiraHolderOn_toFunSnd i)

theorem fderiv_comp_eq_zero (ψ : Chart k α l s U) (i : Fin l) {f : E × ψ.subspace i.castSucc → G}
    (hf : ContDiffMoreiraHolderOn (k - i) α f (ψ.holderSet i.castSucc) (ψ.dom i.castSucc))
    (hf₀ : ∀ x ∈ ψ.holderSet i.castSucc, f x = 0) {x : E × ψ.subspace i.succ}
    (hx : x ∈ ψ.holderSet i.succ) : fderiv ℝ (f ∘ ψ i ∘ .mk x.1) x.2 = 0 := by
  suffices ∀ g : G →L[ℝ] ℝ, g.comp (fderiv ℝ (f ∘ ψ i ∘ .mk x.1) x.2) = 0 by
    ext y
    -- TODO: add `SeparatingDual.ext`
    by_contra hy
    obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hy
    exact hg (DFunLike.congr_fun (this g) y)
  intro g
  rw [← g.fderiv, ← fderiv_comp]
  · refine ψ.fderiv_comp_eq_zero' i (fun a b ↦ g (f (a, b))) ?_ ?_ x.1 x.2 hx
    · exact hf.continuousLinearMap_comp g
    · simp +contextual [hf₀]
  · exact g.differentiableAt
  · apply ContDiffAt.differentiableAt (n := (k - i : ℕ)) _ (by norm_cast; omega)
    apply ((hf.contDiffOn.comp (ψ.contDiffMoreiraHolderOn i).contDiffOn _).contDiffAt _).comp
    · refine contDiffAt_const.prodMk contDiffAt_id
    · exact ψ.mapsTo_dom _
    · exact (ψ.isOpen_dom _).mem_nhds <| ψ.holderSet_subset_dom _ hx

def compUpTo (ψ : Chart k α l s U) (i : Fin (l + 1)) : E × ψ.subspace i → E × F :=
  i.induction (fun xy ↦ (xy.1, xy.2.1) + ψ.center) fun j ↦ (· ∘ ψ j)

theorem compUpTo_zero (ψ : Chart k α l s U) :
    ψ.compUpTo 0 = fun xy ↦ (xy.1, xy.2.1) + ψ.center :=
  rfl

theorem compUpTo_succ (ψ : Chart k α l s U) (i : Fin l) :
    ψ.compUpTo i.succ = ψ.compUpTo i.castSucc ∘ ψ i :=
  rfl
    
theorem contDiffMoreiraHolderOn_compUpTo (ψ : Chart k α l s U) (i : Fin (l + 1)) :
    ContDiffMoreiraHolderOn (k + 1 - i) α (ψ.compUpTo i) (ψ.holderSet i) (ψ.dom i) := by
  induction i using Fin.induction with
  | zero =>
    simp only [compUpTo_zero]
    refine ContDiffOn.contDiffMoreiraHolderOn (.add ?_ contDiffOn_const)
      (ψ.holderSet_subset_dom _) (ψ.isOpen_dom _) (WithTop.coe_lt_top _) _
    exact contDiffOn_fst.prodMk ((ψ.subspace 0).subtypeL.contDiff.comp_contDiffOn contDiffOn_snd)
  | succ i ih =>
    dsimp only [compUpTo_succ]
    refine (ih.of_le ?_).comp ((ψ.contDiffMoreiraHolderOn _).of_le ?_) ?_ ?_ ?_
    · dsimp; omega
    · simp
    · exact ψ.mapsTo_dom _
    · exact ψ.mapsTo_holderSet _
    · omega

theorem mapsTo_compUpTo_dom (ψ : Chart k α l s U) (i : Fin (l + 1)) :
    MapsTo (ψ.compUpTo i) (ψ.dom i) U := by
  induction i using Fin.induction with
  | zero => exact ψ.mapsTo_dom_zero
  | succ i ih => exact ih.comp <| ψ.mapsTo_dom _

theorem compUpTo_fst (ψ : Chart k α l s U) (i : Fin (l + 1)) (x : E × ψ.subspace i) :
    (ψ.compUpTo i x).1 = x.1 + ψ.center.1 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => simp [ih, compUpTo_succ, apply_fst]

theorem dist_le_compUpTo (ψ : Chart k α l s U) (i : Fin (l + 1)) {x : E}
    (hx : x ∈ ball 0 (ψ.radiusLeft i)) {y₁ y₂ : ψ.subspace i}
    (hy₁ : y₁ ∈ ball 0 (ψ.radiusRight i)) (hy₂ : y₂ ∈ ball 0 (ψ.radiusRight i)) :
    dist y₁ y₂ ≤ dist (ψ.compUpTo i (x, y₁)) (ψ.compUpTo i (x, y₂)) := by
  induction i using Fin.induction with
  | zero => simp [compUpTo_zero, Subtype.dist_eq]
  | succ i ih =>
    have H₁ := ψ.mapsTo_dom i (x := (x, y₁)) ⟨hx, hy₁⟩
    have H₂ := ψ.mapsTo_dom i (x := (x, y₂)) ⟨hx, hy₂⟩
    exact (ψ.dist_le_toFunSnd hx hy₁ hy₂).trans <| ih H₁.1 H₁.2 H₂.2

end Chart
