/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monovary
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.FieldSimp

/-!
# Product of convex functions

This file proves that the product of convex functions is convex, provided they monovary.

As corollaries, we also prove that `x ↦ x ^ n` is convex
* `Even.convexOn_pow`: for even `n : ℕ`.
* `convexOn_pow`: over $[0, +∞)$ for `n : ℕ`.
* `convexOn_zpow`: over $(0, +∞)$ For `n : ℤ`.
-/

public section

open Set

variable {𝕜 E F G : Type*}

section LinearOrderedCommRing
variable [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [CommRing E] [LinearOrder E] [IsStrictOrderedRing E]
  [AddCommGroup F] [LinearOrder F] [IsOrderedAddMonoid F]
  [AddCommGroup G] [Module 𝕜 G]
  [Module 𝕜 E] [Module 𝕜 F] [Module E F] [IsScalarTower 𝕜 E F] [SMulCommClass 𝕜 E F]
  [IsOrderedModule 𝕜 F] [IsStrictOrderedModule E F] {s : Set G} {f : G -> E} {g : G -> F}

/--
lemma `ConvexOn.smul'` / 引理 `ConvexOn.smul'`

English:
lemma ConvexOn.smul'
  statement: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x)
  proof: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp
  refine
    (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab) (hf₀ <| hf.1 hx hy ha hb hab) <|
add_nonneg (smul_nonneg ha <| hg₀ hx) smul_nonneg hb hg₀ hy).trans ?_
  calc
      _ = (a * a) • (f x • g x) + (b * b) • (f y • g y)

中文:
引理 ConvexOn.smul'
  结论: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : 对任意 ⦃x⦄, x in s -> 0 <= f x)
  证明: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp
  refine
    (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab) (hf₀ <| hf.1 hx hy ha hb hab) <|
add_nonneg (smul_nonneg ha <| hg₀ hx) smul_nonneg hb hg₀ hy).trans ?_
  calc
      _ = (a * a) • (f x • g x) + (b * b) • (f y • g y)

Depends on / 依赖: add_nonneg, hfg.smul_add_smul_le_smul_add_smul, smul_add_smul_le_smul_add_smul, smul_le_smul, smul_nonneg
-/
lemma ConvexOn.smul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x)
    (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp
  refine
    (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab) (hf₀ <| hf.1 hx hy ha hb hab) <|
add_nonneg (smul_nonneg ha <| hg₀ hx) smul_nonneg hb hg₀ hy).trans ?_
  calc
      _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x) := ?_
    _ <= (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y) := by
        gcongr _ + (a * b) • ?_; exact hfg.smul_add_smul_le_smul_add_smul hx hy
    _ = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y) := by
        simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ = _ := by simp_rw [hab, mul_one]
  simp only [add_smul, smul_add]
  rw [← smul_smul_smul_comm a]; rw [← smul_smul_smul_comm b]; rw [← smul_smul_smul_comm a b]; rw [← smul_smul_smul_comm b b]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_comm b]; rw [add_comm _ ((b * b) • f y • g y)]; rw [add_add_add_comm]; rw [add_comm ((a * b) • f y • g x)]

/--
lemma `ConcaveOn.smul'` / 引理 `ConcaveOn.smul'`

English:
lemma ConcaveOn.smul'
  statement: [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  proof: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp
  refine (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    (add_nonneg (smul_nonneg ha <| hf₀ hx) <| smul_nonneg hb <| hf₀ hy)
    (hg₀ <| hf.1 hx hy ha hb hab)).trans' ?_
  calc a • f x • g x + b • f y • g y
        = (a * 

中文:
引理 ConcaveOn.smul'
  结论: [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  证明: by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp
  refine (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    (add_nonneg (smul_nonneg ha <| hf₀ hx) <| smul_nonneg hb <| hf₀ hy)
    (hg₀ <| hf.1 hx hy ha hb hab)).trans' ?_
  calc a • f x • g x + b • f y • g y
        = (a * 

Depends on / 依赖: add_nonneg, add_smul, mul_add, mul_comm, mul_one, simp_rw, smul_add, smul_le_smul, smul_nonneg
-/
lemma ConcaveOn.smul' [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp
  refine (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    (add_nonneg (smul_nonneg ha <| hf₀ hx) <| smul_nonneg hb <| hf₀ hy)
    (hg₀ <| hf.1 hx hy ha hb hab)).trans' ?_
  calc a • f x • g x + b • f y • g y
        = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y) := by simp_rw [hab, mul_one]
    _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y) := by
        simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ <= (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x) := by
        gcongr _ + (a * b) • ?_; exact hfg.smul_add_smul_le_smul_add_smul hx hy
    _ = _ := ?_
  simp only [add_smul, smul_add]
  rw [← smul_smul_smul_comm a]; rw [← smul_smul_smul_comm b]; rw [← smul_smul_smul_comm a b]; rw [← smul_smul_smul_comm b b]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_comm b a]; rw [add_comm ((a * b) • f x • g y)]; rw [add_comm ((a * b) • f x • g y)]; rw [add_add_add_comm]

/--
lemma `ConvexOn.smul''` / 引理 `ConvexOn.smul''`

English:
lemma ConvexOn.smul''
  statement: [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  proof: by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx => neg_nonneg.2 <| hf₀ hx) (fun x hx => neg_nonneg.2 <| hg₀ hx)
    hfg.neg

中文:
引理 ConvexOn.smul''
  结论: [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  证明: by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx => neg_nonneg.2 <| hf₀ hx) (fun x hx => neg_nonneg.2 <| hg₀ hx)
    hfg.neg

Depends on / 依赖: hf.neg.smul, hfg.neg, hg.neg, neg_nonneg, neg_smul_neg
-/
lemma ConvexOn.smul'' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx => neg_nonneg.2 <| hf₀ hx) (fun x hx => neg_nonneg.2 <| hg₀ hx)
    hfg.neg

/--
lemma `ConcaveOn.smul''` / 引理 `ConcaveOn.smul''`

English:
lemma ConcaveOn.smul''
  statement: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0)
  proof: by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx => neg_nonneg.2 <| hf₀ hx) (fun x hx => neg_nonneg.2 <| hg₀ hx)
    hfg.neg

中文:
引理 ConcaveOn.smul''
  结论: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : 对任意 ⦃x⦄, x in s -> f x <= 0)
  证明: by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx => neg_nonneg.2 <| hf₀ hx) (fun x hx => neg_nonneg.2 <| hg₀ hx)
    hfg.neg

Depends on / 依赖: hf.neg.smul, hfg.neg, hg.neg, neg_nonneg, neg_smul_neg
-/
lemma ConcaveOn.smul'' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0)
    (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) := by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx => neg_nonneg.2 <| hf₀ hx) (fun x hx => neg_nonneg.2 <| hg₀ hx)
    hfg.neg

/--
lemma `ConvexOn.smul_concaveOn` / 引理 `ConvexOn.smul_concaveOn`

English:
lemma ConvexOn.smul_concaveOn
  statement: (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  proof: by
  rw [← neg_convexOn_iff]; rw [← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx => neg_nonneg.2 <| hg₀ hx) hfg.neg_right

中文:
引理 ConvexOn.smul_concaveOn
  结论: (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  证明: by
  rw [← neg_convexOn_iff]; rw [← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx => neg_nonneg.2 <| hg₀ hx) hfg.neg_right

Depends on / 依赖: hf.smul, hfg.neg_right, hg.neg, neg_convexOn_iff, neg_nonneg, neg_right, smul_neg
-/
lemma ConvexOn.smul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [← neg_convexOn_iff]; rw [← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx => neg_nonneg.2 <| hg₀ hx) hfg.neg_right

/--
lemma `ConcaveOn.smul_convexOn` / 引理 `ConcaveOn.smul_convexOn`

English:
lemma ConcaveOn.smul_convexOn
  statement: [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  proof: by
  rw [← neg_concaveOn_iff]; rw [← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx => neg_nonneg.2 <| hg₀ hx) hfg.neg_right

中文:
引理 ConcaveOn.smul_convexOn
  结论: [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  证明: by
  rw [← neg_concaveOn_iff]; rw [← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx => neg_nonneg.2 <| hg₀ hx) hfg.neg_right

Depends on / 依赖: hf.smul, hfg.neg_right, hg.neg, neg_concaveOn_iff, neg_nonneg, neg_right, smul_neg
-/
lemma ConcaveOn.smul_convexOn [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) := by
  rw [← neg_concaveOn_iff]; rw [← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx => neg_nonneg.2 <| hg₀ hx) hfg.neg_right

/--
lemma `ConvexOn.smul_concaveOn'` / 引理 `ConvexOn.smul_concaveOn'`

English:
lemma ConvexOn.smul_concaveOn'
  statement: [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  proof: by
  rw [← neg_concaveOn_iff]; rw [← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx => neg_nonpos.2 <| hg₀ hx) hfg.neg_right

中文:
引理 ConvexOn.smul_concaveOn'
  结论: [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  证明: by
  rw [← neg_concaveOn_iff]; rw [← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx => neg_nonpos.2 <| hg₀ hx) hfg.neg_right

Depends on / 依赖: hf.smul, hfg.neg_right, hg.neg, neg_concaveOn_iff, neg_nonpos, neg_right, smul_neg
-/
lemma ConvexOn.smul_concaveOn' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) := by
  rw [← neg_concaveOn_iff]; rw [← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx => neg_nonpos.2 <| hg₀ hx) hfg.neg_right

/--
lemma `ConcaveOn.smul_convexOn'` / 引理 `ConcaveOn.smul_convexOn'`

English:
lemma ConcaveOn.smul_convexOn'
  statement: (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  proof: by
  rw [← neg_convexOn_iff]; rw [← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx => neg_nonpos.2 <| hg₀ hx) hfg.neg_right

中文:
引理 ConcaveOn.smul_convexOn'
  结论: (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  证明: by
  rw [← neg_convexOn_iff]; rw [← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx => neg_nonpos.2 <| hg₀ hx) hfg.neg_right

Depends on / 依赖: hf.smul, hfg.neg_right, hg.neg, neg_convexOn_iff, neg_nonpos, neg_right, smul_neg
-/
lemma ConcaveOn.smul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [← neg_convexOn_iff]; rw [← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx => neg_nonpos.2 <| hg₀ hx) hfg.neg_right

variable [IsOrderedModule 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E] {f g : G -> E}

/--
lemma `ConvexOn.mul` / 引理 `ConvexOn.mul`

English:
lemma ConvexOn.mul
  statement: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x)
  proof: hf.smul' hg hf₀ hg₀ hfg

中文:
引理 ConvexOn.mul
  结论: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : 对任意 ⦃x⦄, x in s -> 0 <= f x)
  证明: hf.smul' hg hf₀ hg₀ hfg

Depends on / 依赖: hf.smul
-/
lemma ConvexOn.mul (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x)
    (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul' hg hf₀ hg₀ hfg

/--
lemma `ConcaveOn.mul` / 引理 `ConcaveOn.mul`

English:
lemma ConcaveOn.mul
  statement: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  proof: hf.smul' hg hf₀ hg₀ hfg

中文:
引理 ConcaveOn.mul
  结论: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  证明: hf.smul' hg hf₀ hg₀ hfg

Depends on / 依赖: hf.smul
-/
lemma ConcaveOn.mul (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul' hg hf₀ hg₀ hfg

/--
lemma `ConvexOn.mul'` / 引理 `ConvexOn.mul'`

English:
lemma ConvexOn.mul'
  statement: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0)
  proof: hf.smul'' hg hf₀ hg₀ hfg

中文:
引理 ConvexOn.mul'
  结论: (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : 对任意 ⦃x⦄, x in s -> f x <= 0)
  证明: hf.smul'' hg hf₀ hg₀ hfg

Depends on / 依赖: hf.smul
-/
lemma ConvexOn.mul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0)
    (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul'' hg hf₀ hg₀ hfg

/--
lemma `ConcaveOn.mul'` / 引理 `ConcaveOn.mul'`

English:
lemma ConcaveOn.mul'
  statement: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0)
  proof: hf.smul'' hg hf₀ hg₀ hfg

中文:
引理 ConcaveOn.mul'
  结论: (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : 对任意 ⦃x⦄, x in s -> f x <= 0)
  证明: hf.smul'' hg hf₀ hg₀ hfg

Depends on / 依赖: hf.smul
-/
lemma ConcaveOn.mul' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0)
    (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul'' hg hf₀ hg₀ hfg

/--
lemma `ConvexOn.mul_concaveOn` / 引理 `ConvexOn.mul_concaveOn`

English:
lemma ConvexOn.mul_concaveOn
  statement: (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  proof: hf.smul_concaveOn hg hf₀ hg₀ hfg

中文:
引理 ConvexOn.mul_concaveOn
  结论: (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  证明: hf.smul_concaveOn hg hf₀ hg₀ hfg

Depends on / 依赖: hf.smul_concaveOn, smul_concaveOn
-/
lemma ConvexOn.mul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul_concaveOn hg hf₀ hg₀ hfg

/--
lemma `ConcaveOn.mul_convexOn` / 引理 `ConcaveOn.mul_convexOn`

English:
lemma ConcaveOn.mul_convexOn
  statement: (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  proof: hf.smul_convexOn hg hf₀ hg₀ hfg

中文:
引理 ConcaveOn.mul_convexOn
  结论: (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  证明: hf.smul_convexOn hg hf₀ hg₀ hfg

Depends on / 依赖: hf.smul_convexOn, smul_convexOn
-/
lemma ConcaveOn.mul_convexOn (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul_convexOn hg hf₀ hg₀ hfg

/--
lemma `ConvexOn.mul_concaveOn'` / 引理 `ConvexOn.mul_concaveOn'`

English:
lemma ConvexOn.mul_concaveOn'
  statement: (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  proof: hf.smul_concaveOn' hg hf₀ hg₀ hfg

中文:
引理 ConvexOn.mul_concaveOn'
  结论: (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
  证明: hf.smul_concaveOn' hg hf₀ hg₀ hfg

Depends on / 依赖: hf.smul_concaveOn, smul_concaveOn
-/
lemma ConvexOn.mul_concaveOn' (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul_concaveOn' hg hf₀ hg₀ hfg

/--
lemma `ConcaveOn.mul_convexOn'` / 引理 `ConcaveOn.mul_convexOn'`

English:
lemma ConcaveOn.mul_convexOn'
  statement: (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  proof: hf.smul_convexOn' hg hf₀ hg₀ hfg

中文:
引理 ConcaveOn.mul_convexOn'
  结论: (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
  证明: hf.smul_convexOn' hg hf₀ hg₀ hfg

Depends on / 依赖: hf.smul_convexOn, smul_convexOn
-/
lemma ConcaveOn.mul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := hf.smul_convexOn' hg hf₀ hg₀ hfg

/--
lemma `ConvexOn.pow` / 引理 `ConvexOn.pow`

English:
lemma ConvexOn.pow
  given: (hf : ConvexOn 𝕜 s f) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x)

中文:
引理 ConvexOn.pow
  条件: (hf : ConvexOn 𝕜 s f) (hf₀ : 对任意 ⦃x⦄, x in s -> 0 <= f x)
-/
lemma ConvexOn.pow (hf : ConvexOn 𝕜 s f) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) :
    forall n, ConvexOn 𝕜 s (f ^ n)
  | 0 => by simpa using! convexOn_const 1 hf.1
  | n + 1 => by
    rw [pow_succ']
exact hf.mul (hf.pow hf₀ _) hf₀ (fun x hx => pow_nonneg (hf₀ hx) _)
      (monovaryOn_self f s).pow_right₀ hf₀ n

/--
lemma `convexOn_pow` / 引理 `convexOn_pow`

English:
lemma convexOn_pow
  statement: forall n, ConvexOn 𝕜 (Ici 0) fun x : 𝕜 => x ^ n
  proof: (convexOn_id <| convex_Ici _).pow fun _ => id

中文:
引理 convexOn_pow
  结论: 对任意 n, ConvexOn 𝕜 (Ici 0) fun x : 𝕜 => x ^ n
  证明: (convexOn_id <| convex_Ici _).pow fun _ => id

Depends on / 依赖: convexOn_id, convex_Ici
-/
lemma convexOn_pow : forall n, ConvexOn 𝕜 (Ici 0) fun x : 𝕜 => x ^ n :=
  (convexOn_id <| convex_Ici _).pow fun _ => id

/--
lemma `Even.convexOn_pow` / 引理 `Even.convexOn_pow`

English:
lemma Even.convexOn_pow
  given: {n : Nat} (hn : Even n)
  statement: ConvexOn 𝕜 univ fun x : 𝕜 => x ^ n
  proof: by
  obtain ⟨n, rfl⟩ := hn
  simp_rw [← two_mul, pow_mul]
  refine ConvexOn.pow ⟨convex_univ, fun x _ y _ a b ha hb hab => sub_nonneg.1 ?_⟩
    (fun _ _ => by positivity) _
  calc
    (0 : 𝕜) <= (a * b) * (x - y) ^ 2 := by positivity
    _ = _ := by obtain rfl := eq_sub_of_add_eq hab; simp only [smu

中文:
引理 Even.convexOn_pow
  条件: {n : 自然数} (hn : Even n)
  结论: ConvexOn 𝕜 univ fun x : 𝕜 => x ^ n
  证明: by
  obtain ⟨n, rfl⟩ := hn
  simp_rw [← two_mul, pow_mul]
  refine ConvexOn.pow ⟨convex_univ, fun x _ y _ a b ha hb hab => sub_nonneg.1 ?_⟩
    (fun _ _ => by positivity) _
  calc
    (0 : 𝕜) <= (a * b) * (x - y) ^ 2 := by positivity
    _ = _ := by obtain rfl := eq_sub_of_add_eq hab; simp only [smu
-/
protected lemma Even.convexOn_pow {n : Nat} (hn : Even n) : ConvexOn 𝕜 univ fun x : 𝕜 => x ^ n := by
  obtain ⟨n, rfl⟩ := hn
  simp_rw [← two_mul, pow_mul]
  refine ConvexOn.pow ⟨convex_univ, fun x _ y _ a b ha hb hab => sub_nonneg.1 ?_⟩
    (fun _ _ => by positivity) _
  calc
    (0 : 𝕜) <= (a * b) * (x - y) ^ 2 := by positivity
    _ = _ := by obtain rfl := eq_sub_of_add_eq hab; simp only [smul_eq_mul]; ring

end LinearOrderedCommRing

section LinearOrderedField
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

open Int in
/--
lemma `convexOn_zpow` / 引理 `convexOn_zpow`

English:
lemma convexOn_zpow
  statement: forall n : Int, ConvexOn 𝕜 (Ioi 0) fun x : 𝕜 => x ^ n
  proof: by positivity
    linear_combination H - x * y * (a + b + 1) * hab

中文:
引理 convexOn_zpow
  结论: 对任意 n : 整数, ConvexOn 𝕜 (Ioi 0) fun x : 𝕜 => x ^ n
  证明: by positivity
    linear_combination H - x * y * (a + b + 1) * hab

Depends on / 依赖: linear_combination
-/
lemma convexOn_zpow : forall n : Int, ConvexOn 𝕜 (Ioi 0) fun x : 𝕜 => x ^ n
  | (n : Nat) => by
    simp_rw [zpow_natCast]
    exact (convexOn_pow n).subset Ioi_subset_Ici_self (convex_Ioi _)
  | -[n+1] => by
    simp_rw [zpow_negSucc, ← inv_pow]
    refine (convexOn_iff_forall_pos.2 ⟨convex_Ioi _, ?_⟩).pow (fun x (hx : 0 < x) => by positivity) _
    rintro x (hx : 0 < x) y (hy : 0 < y) a b ha hb hab
    simp only [smul_eq_mul]
    field_simp
    have H : 0 <= a * b * (x - y) ^ 2 := by positivity
    linear_combination H - x * y * (a + b + 1) * hab

end LinearOrderedField
