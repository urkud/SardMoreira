import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.Semicontinuous

open Set Filter Function TopologicalSpace

namespace Topology

namespace WithLower

section Preorder

variable {α : Type*} [Preorder α] {a b : α}

@[simp] theorem toLower_le_toLower : toLower a ≤ toLower b ↔ a ≤ b := .rfl
@[simp] theorem toLower_lt_toLower : toLower a < toLower b ↔ a < b := .rfl

@[fun_prop]
theorem continuous_toLower [TopologicalSpace α] [ClosedIciTopology α] :
    Continuous (toLower : α → WithLower α) :=
  continuous_generateFrom_iff.mpr <| by rintro _ ⟨a, rfl⟩; exact isClosed_Ici.isOpen_compl

end Preorder

instance {α} [PartialOrder α] : PartialOrder (WithLower α) := ‹_›
instance {α} [LinearOrder α] : LinearOrder (WithLower α) := ‹_›

end WithLower

namespace WithUpper

section Preorder

variable {α : Type*} [Preorder α] {a b : α}

@[simp] theorem toUpper_le_toUpper : toUpper a ≤ toUpper b ↔ a ≤ b := .rfl
@[simp] theorem toUpper_lt_toUpper : toUpper a < toUpper b ↔ a < b := .rfl

@[fun_prop]
theorem continuous_toUpper [TopologicalSpace α] [ClosedIicTopology α] :
    Continuous (toUpper : α → WithUpper α) :=
  WithLower.continuous_toLower (α := αᵒᵈ)

end Preorder

instance {α} [PartialOrder α] : PartialOrder (WithUpper α) := ‹_›
instance {α} [LinearOrder α] : LinearOrder (WithUpper α) := ‹_›

end WithUpper

theorem IsLower.tendsto_nhds_iff_not_le {α X : Type*} [Preorder X] [TopologicalSpace X] [IsLower X]
    {f : α → X} {l : Filter α} {x : X} :
    Tendsto f l (𝓝 x) ↔ ∀ y, ¬y ≤ x → ∀ᶠ z in l, ¬y ≤ f z := by
  simp [topology_eq_lowerTopology, tendsto_nhds_generateFrom_iff, Filter.Eventually, Ici,
    compl_setOf]

theorem IsLower.tendsto_nhds_iff_lt {α X : Type*} [LinearOrder X] [TopologicalSpace X] [IsLower X]
    {f : α → X} {l : Filter α} {x : X} :
    Tendsto f l (𝓝 x) ↔ ∀ y, x < y → ∀ᶠ z in l, f z < y := by
  simp only [IsLower.tendsto_nhds_iff_not_le, not_le]

theorem IsUpper.tendsto_nhds_iff_not_le {α X : Type*} [Preorder X] [TopologicalSpace X] [IsUpper X]
    {f : α → X} {l : Filter α} {x : X} : Tendsto f l (𝓝 x) ↔ ∀ y, ¬x ≤ y → ∀ᶠ z in l, ¬f z ≤ y :=
  IsLower.tendsto_nhds_iff_not_le (X := Xᵒᵈ)

theorem IsUpper.tendsto_nhds_iff_lt {α X : Type*} [LinearOrder X] [TopologicalSpace X] [IsUpper X]
    {f : α → X} {l : Filter α} {x : X} : Tendsto f l (𝓝 x) ↔ ∀ y < x, ∀ᶠ z in l, y < f z :=
  IsLower.tendsto_nhds_iff_lt (X := Xᵒᵈ)

variable {X Y : Type*} [TopologicalSpace X] [LinearOrder Y] {f : X → Y} {s : Set X} {x : X}

theorem continuousWithinAt_toLower_comp_iff :
    ContinuousWithinAt (WithLower.toLower ∘ f) s x ↔ UpperSemicontinuousWithinAt f s x :=
  IsLower.tendsto_nhds_iff_lt

theorem continuousWithinAt_toUpper_comp_iff :
    ContinuousWithinAt (WithUpper.toUpper ∘ f) s x ↔ LowerSemicontinuousWithinAt f s x :=
  IsUpper.tendsto_nhds_iff_lt

theorem continuousAt_toLower_comp_iff :
    ContinuousAt (WithLower.toLower ∘ f) x ↔ UpperSemicontinuousAt f x :=
  IsLower.tendsto_nhds_iff_lt

theorem continuousAt_toUpper_comp_iff :
    ContinuousAt (WithUpper.toUpper ∘ f) x ↔ LowerSemicontinuousAt f x :=
  IsUpper.tendsto_nhds_iff_lt

theorem continuousOn_toLower_comp_iff :
    ContinuousOn (WithLower.toLower ∘ f) s ↔ UpperSemicontinuousOn f s :=
  forall₂_congr fun _ _ ↦ continuousWithinAt_toLower_comp_iff

theorem continuousOn_toUpper_comp_iff :
    ContinuousOn (WithUpper.toUpper ∘ f) s ↔ LowerSemicontinuousOn f s :=
  forall₂_congr fun _ _ ↦ continuousWithinAt_toUpper_comp_iff

theorem continuous_toLower_comp_iff : Continuous (WithLower.toLower ∘ f) ↔ UpperSemicontinuous f :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ continuousAt_toLower_comp_iff

theorem continuous_toUpper_comp_iff : Continuous (WithUpper.toUpper ∘ f) ↔ LowerSemicontinuous f :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ continuousAt_toUpper_comp_iff

end Topology

theorem LowerSemicontinuousOn.exists_isMinOn {X α : Type*} [TopologicalSpace X] [LinearOrder α]
    {f : X → α} {s : Set X} (hf : LowerSemicontinuousOn f s) (hs : IsCompact s) (hne : s.Nonempty) :
    ∃ x ∈ s, IsMinOn f s x := by
  rw [← Topology.continuousOn_toUpper_comp_iff] at hf
  exact hs.exists_isMinOn (f := Topology.WithUpper.toUpper ∘ f) hne hf
