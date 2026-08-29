/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Malo Jaffré
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Slopes of convex functions

This file relates convexity/concavity of functions in a linearly ordered field and the monotonicity
of their slopes.

The main use is to show convexity/concavity from monotonicity of the derivative.
-/

public section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 -> 𝕜}

/--
theorem `ConvexOn.slope_mono_adjacent` / 定理 `ConvexOn.slope_mono_adjacent`

English:
theorem ConvexOn.slope_mono_adjacent
  statement: (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  proof: by
  have hxz := hxy.trans hyz
  rw [← sub_pos] at hxy hxz hyz
  have ha : 0 <= (z - y) / (z - x) := by positivity
  have hb : 0 <= (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz ha hb (by field)
  simp only [smul_eq_mul] at key
  ring_nf at key
  field_simp at key ⊢
  linarith

中文:
定理 ConvexOn.slope_mono_adjacent
  结论: (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  证明: by
  have hxz := hxy.trans hyz
  rw [← sub_pos] at hxy hxz hyz
  have ha : 0 <= (z - y) / (z - x) := by positivity
  have hb : 0 <= (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz ha hb (by field)
  simp only [smul_eq_mul] at key
  ring_nf at key
  field_simp at key ⊢
  linarith

Depends on / 依赖: hxy.trans, ring_nf, smul_eq_mul, sub_pos
-/
theorem ConvexOn.slope_mono_adjacent (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
    (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) <= (f z - f y) / (z - y) := by
  have hxz := hxy.trans hyz
  rw [← sub_pos] at hxy hxz hyz
  have ha : 0 <= (z - y) / (z - x) := by positivity
  have hb : 0 <= (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz ha hb (by field)
  simp only [smul_eq_mul] at key
  ring_nf at key
  field_simp at key ⊢
  linarith

/--
theorem `ConcaveOn.slope_anti_adjacent` / 定理 `ConcaveOn.slope_anti_adjacent`

English:
theorem ConcaveOn.slope_anti_adjacent
  statement: (hf : ConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  proof: by
  have := ConvexOn.slope_mono_adjacent hf.neg hx hz hxy hyz
  simp only [Pi.neg_apply] at this
  linear_combination this

中文:
定理 ConcaveOn.slope_anti_adjacent
  结论: (hf : ConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  证明: by
  have := ConvexOn.slope_mono_adjacent hf.neg hx hz hxy hyz
  simp only [Pi.neg_apply] at this
  linear_combination this

Depends on / 依赖: ConvexOn, ConvexOn.slope_mono_adjacent, Pi.neg_apply, hf.neg, linear_combination, neg_apply, slope_mono_adjacent
-/
theorem ConcaveOn.slope_anti_adjacent (hf : ConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
    (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) <= (f y - f x) / (y - x) := by
  have := ConvexOn.slope_mono_adjacent hf.neg hx hz hxy hyz
  simp only [Pi.neg_apply] at this
  linear_combination this

/--
theorem `StrictConvexOn.slope_strict_mono_adjacent` / 定理 `StrictConvexOn.slope_strict_mono_adjacent`

English:
theorem StrictConvexOn.slope_strict_mono_adjacent
  statement: (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜}
  proof: by
  have hxz := hxy.trans hyz
  have hxz' := hxz.ne
  rw [← sub_pos] at hxy hxz hyz
  have ha : 0 < (z - y) / (z - x) := by positivity
  have hb : 0 < (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz hxz' ha hb (by field)
  simp only [smul_eq_mul] at key
  ring_nf at key
  field_simp at 

中文:
定理 StrictConvexOn.slope_strict_mono_adjacent
  结论: (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜}
  证明: by
  have hxz := hxy.trans hyz
  have hxz' := hxz.ne
  rw [← sub_pos] at hxy hxz hyz
  have ha : 0 < (z - y) / (z - x) := by positivity
  have hb : 0 < (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz hxz' ha hb (by field)
  simp only [smul_eq_mul] at key
  ring_nf at key
  field_simp at 

Depends on / 依赖: hxy.trans, hxz.ne, ring_nf, smul_eq_mul, sub_pos
-/
theorem StrictConvexOn.slope_strict_mono_adjacent (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜}
    (hx : x in s) (hz : z in s) (hxy : x < y) (hyz : y < z) :
    (f y - f x) / (y - x) < (f z - f y) / (z - y) := by
  have hxz := hxy.trans hyz
  have hxz' := hxz.ne
  rw [← sub_pos] at hxy hxz hyz
  have ha : 0 < (z - y) / (z - x) := by positivity
  have hb : 0 < (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz hxz' ha hb (by field)
  simp only [smul_eq_mul] at key
  ring_nf at key
  field_simp at key ⊢
  linarith

/--
theorem `StrictConcaveOn.slope_anti_adjacent` / 定理 `StrictConcaveOn.slope_anti_adjacent`

English:
theorem StrictConcaveOn.slope_anti_adjacent
  statement: (hf : StrictConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
  proof: by
  have := StrictConvexOn.slope_strict_mono_adjacent hf.neg hx hz hxy hyz
  simp only [Pi.neg_apply] at this
  linear_combination this

中文:
定理 StrictConcaveOn.slope_anti_adjacent
  结论: (hf : StrictConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
  证明: by
  have := StrictConvexOn.slope_strict_mono_adjacent hf.neg hx hz hxy hyz
  simp only [Pi.neg_apply] at this
  linear_combination this

Depends on / 依赖: Pi.neg_apply, StrictConvexOn, StrictConvexOn.slope_strict_mono_adjacent, hf.neg, linear_combination, neg_apply, slope_strict_mono_adjacent
-/
theorem StrictConcaveOn.slope_anti_adjacent (hf : StrictConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
    (hz : z in s) (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) < (f y - f x) / (y - x) := by
  have := StrictConvexOn.slope_strict_mono_adjacent hf.neg hx hz hxy hyz
  simp only [Pi.neg_apply] at this
  linear_combination this

/--
theorem `convexOn_of_slope_mono_adjacent` / 定理 `convexOn_of_slope_mono_adjacent`

English:
theorem convexOn_of_slope_mono_adjacent
  statement: (hs : Convex 𝕜 s)
  proof: LinearOrder.convexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    simp only [smul_eq_mul]
    have hxy : x < a * x + b * z := by linear_combination b * hxz - x * hab
    have hyz : a * x + b * z < z := by linear_combination a * hxz + z * hab
    have key := hf hx hz hxy hyz
    field_simp [sub

中文:
定理 convexOn_of_slope_mono_adjacent
  结论: (hs : 凸 𝕜 s)
  证明: LinearOrder.convexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    simp only [smul_eq_mul]
    have hxy : x < a * x + b * z := by linear_combination b * hxz - x * hab
    have hyz : a * x + b * z < z := by linear_combination a * hxz + z * hab
    have key := hf hx hz hxy hyz
    field_simp [sub

Depends on / 依赖: LinearOrder, LinearOrder.convexOn_of_lt, convexOn_of_lt, le_of_mul_le_mul_left, linear_combination, smul_eq_mul, sub_pos
-/
theorem convexOn_of_slope_mono_adjacent (hs : Convex 𝕜 s)
    (hf :
      forall {x y z : 𝕜},
        x in s -> z in s -> x < y -> y < z -> (f y - f x) / (y - x) <= (f z - f y) / (z - y)) :
    ConvexOn 𝕜 s f :=
  LinearOrder.convexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    simp only [smul_eq_mul]
    have hxy : x < a * x + b * z := by linear_combination b * hxz - x * hab
    have hyz : a * x + b * z < z := by linear_combination a * hxz + z * hab
    have key := hf hx hz hxy hyz
    field_simp [sub_pos.2 hxy, sub_pos.2 hyz] at key
    apply le_of_mul_le_mul_left ?_ (sub_pos.2 hxz)
    linear_combination key + (- f x * z + x * f z) * hab

/--
theorem `concaveOn_of_slope_anti_adjacent` / 定理 `concaveOn_of_slope_anti_adjacent`

English:
theorem concaveOn_of_slope_anti_adjacent
  statement: (hs : Convex 𝕜 s)
  proof: by
  rw [← neg_convexOn_iff]
  refine convexOn_of_slope_mono_adjacent hs fun hx hz hxy hyz => ?_
  simp only [Pi.neg_apply]
  linear_combination hf hx hz hxy hyz

中文:
定理 concaveOn_of_slope_anti_adjacent
  结论: (hs : 凸 𝕜 s)
  证明: by
  rw [← neg_convexOn_iff]
  refine convexOn_of_slope_mono_adjacent hs fun hx hz hxy hyz => ?_
  simp only [Pi.neg_apply]
  linear_combination hf hx hz hxy hyz

Depends on / 依赖: Pi.neg_apply, convexOn_of_slope_mono_adjacent, linear_combination, neg_apply, neg_convexOn_iff
-/
theorem concaveOn_of_slope_anti_adjacent (hs : Convex 𝕜 s)
    (hf :
      forall {x y z : 𝕜},
        x in s -> z in s -> x < y -> y < z -> (f z - f y) / (z - y) <= (f y - f x) / (y - x)) :
    ConcaveOn 𝕜 s f := by
  rw [← neg_convexOn_iff]
  refine convexOn_of_slope_mono_adjacent hs fun hx hz hxy hyz => ?_
  simp only [Pi.neg_apply]
  linear_combination hf hx hz hxy hyz

/--
theorem `strictConvexOn_of_slope_strict_mono_adjacent` / 定理 `strictConvexOn_of_slope_strict_mono_adjacent`

English:
theorem strictConvexOn_of_slope_strict_mono_adjacent
  statement: (hs : Convex 𝕜 s)
  proof: LinearOrder.strictConvexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    simp only [smul_eq_mul]
    have hxy : x < a * x + b * z := by linear_combination b * hxz - x * hab
    have hyz : a * x + b * z < z := by linear_combination a * hxz + z * hab
    have key := hf hx hz hxy hyz
    field_sim

中文:
定理 strictConvexOn_of_slope_strict_mono_adjacent
  结论: (hs : 凸 𝕜 s)
  证明: LinearOrder.strictConvexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    simp only [smul_eq_mul]
    have hxy : x < a * x + b * z := by linear_combination b * hxz - x * hab
    have hyz : a * x + b * z < z := by linear_combination a * hxz + z * hab
    have key := hf hx hz hxy hyz
    field_sim

Depends on / 依赖: LinearOrder, LinearOrder.strictConvexOn_of_lt, linear_combination, lt_of_mul_lt_mul_left, smul_eq_mul, strictConvexOn_of_lt, sub_pos
-/
theorem strictConvexOn_of_slope_strict_mono_adjacent (hs : Convex 𝕜 s)
    (hf :
      forall {x y z : 𝕜},
        x in s -> z in s -> x < y -> y < z -> (f y - f x) / (y - x) < (f z - f y) / (z - y)) :
    StrictConvexOn 𝕜 s f :=
  LinearOrder.strictConvexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    simp only [smul_eq_mul]
    have hxy : x < a * x + b * z := by linear_combination b * hxz - x * hab
    have hyz : a * x + b * z < z := by linear_combination a * hxz + z * hab
    have key := hf hx hz hxy hyz
    field_simp [sub_pos.2 hxy, sub_pos.2 hyz] at key
    apply lt_of_mul_lt_mul_left ?_ (sub_pos.2 hxz).le
    linear_combination key + (- f x * z + x * f z) * hab

/--
theorem `strictConcaveOn_of_slope_strict_anti_adjacent` / 定理 `strictConcaveOn_of_slope_strict_anti_adjacent`

English:
theorem strictConcaveOn_of_slope_strict_anti_adjacent
  statement: (hs : Convex 𝕜 s)
  proof: by
  rw [← neg_strictConvexOn_iff]
  refine strictConvexOn_of_slope_strict_mono_adjacent hs fun hx hz hxy hyz => ?_
  simp only [Pi.neg_apply]
  linear_combination hf hx hz hxy hyz

中文:
定理 strictConcaveOn_of_slope_strict_anti_adjacent
  结论: (hs : 凸 𝕜 s)
  证明: by
  rw [← neg_strictConvexOn_iff]
  refine strictConvexOn_of_slope_strict_mono_adjacent hs fun hx hz hxy hyz => ?_
  simp only [Pi.neg_apply]
  linear_combination hf hx hz hxy hyz

Depends on / 依赖: Pi.neg_apply, linear_combination, neg_apply, neg_strictConvexOn_iff, strictConvexOn_of_slope_strict_mono_adjacent
-/
theorem strictConcaveOn_of_slope_strict_anti_adjacent (hs : Convex 𝕜 s)
    (hf :
      forall {x y z : 𝕜},
        x in s -> z in s -> x < y -> y < z -> (f z - f y) / (z - y) < (f y - f x) / (y - x)) :
    StrictConcaveOn 𝕜 s f := by
  rw [← neg_strictConvexOn_iff]
  refine strictConvexOn_of_slope_strict_mono_adjacent hs fun hx hz hxy hyz => ?_
  simp only [Pi.neg_apply]
  linear_combination hf hx hz hxy hyz

/--
theorem `convexOn_iff_slope_mono_adjacent` / 定理 `convexOn_iff_slope_mono_adjacent`

English:
theorem convexOn_iff_slope_mono_adjacent
  proof: ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_mono_adjacent⟩, fun h =>
    convexOn_of_slope_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

中文:
定理 convexOn_iff_slope_mono_adjacent
  证明: ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_mono_adjacent⟩, fun h =>
    convexOn_of_slope_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

Depends on / 依赖: convexOn_of_slope_mono_adjacent, h.slope_mono_adjacent, slope_mono_adjacent
-/
theorem convexOn_iff_slope_mono_adjacent :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ forall ⦃x y z : 𝕜⦄,
          x in s -> z in s -> x < y -> y < z -> (f y - f x) / (y - x) <= (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_mono_adjacent⟩, fun h =>
    convexOn_of_slope_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

/--
theorem `concaveOn_iff_slope_anti_adjacent` / 定理 `concaveOn_iff_slope_anti_adjacent`

English:
theorem concaveOn_iff_slope_anti_adjacent
  proof: ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    concaveOn_of_slope_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

中文:
定理 concaveOn_iff_slope_anti_adjacent
  证明: ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    concaveOn_of_slope_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

Depends on / 依赖: concaveOn_of_slope_anti_adjacent, h.slope_anti_adjacent, slope_anti_adjacent
-/
theorem concaveOn_iff_slope_anti_adjacent :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        forall ⦃x y z : 𝕜⦄,
          x in s -> z in s -> x < y -> y < z -> (f z - f y) / (z - y) <= (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    concaveOn_of_slope_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

/--
theorem `strictConvexOn_iff_slope_strict_mono_adjacent` / 定理 `strictConvexOn_iff_slope_strict_mono_adjacent`

English:
theorem strictConvexOn_iff_slope_strict_mono_adjacent
  proof: ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_strict_mono_adjacent⟩, fun h =>
    strictConvexOn_of_slope_strict_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

中文:
定理 strictConvexOn_iff_slope_strict_mono_adjacent
  证明: ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_strict_mono_adjacent⟩, fun h =>
    strictConvexOn_of_slope_strict_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

Depends on / 依赖: h.slope_strict_mono_adjacent, slope_strict_mono_adjacent, strictConvexOn_of_slope_strict_mono_adjacent
-/
theorem strictConvexOn_iff_slope_strict_mono_adjacent :
    StrictConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        forall ⦃x y z : 𝕜⦄,
          x in s -> z in s -> x < y -> y < z -> (f y - f x) / (y - x) < (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_strict_mono_adjacent⟩, fun h =>
    strictConvexOn_of_slope_strict_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

/--
theorem `strictConcaveOn_iff_slope_strict_anti_adjacent` / 定理 `strictConcaveOn_iff_slope_strict_anti_adjacent`

English:
theorem strictConcaveOn_iff_slope_strict_anti_adjacent
  proof: ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    strictConcaveOn_of_slope_strict_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

中文:
定理 strictConcaveOn_iff_slope_strict_anti_adjacent
  证明: ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    strictConcaveOn_of_slope_strict_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

Depends on / 依赖: h.slope_anti_adjacent, slope_anti_adjacent, strictConcaveOn_of_slope_strict_anti_adjacent
-/
theorem strictConcaveOn_iff_slope_strict_anti_adjacent :
    StrictConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        forall ⦃x y z : 𝕜⦄,
          x in s -> z in s -> x < y -> y < z -> (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    strictConcaveOn_of_slope_strict_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

/--
theorem `ConvexOn.secant_mono_aux1` / 定理 `ConvexOn.secant_mono_aux1`

English:
theorem ConvexOn.secant_mono_aux1
  statement: (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  proof: by
  have hxy' : 0 < y - x := by linarith
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  have ha : 0 <= (z - y) / (z - x) := by positivity
  have hb : 0 <= (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz ha hb ?_
  · simp only [smul_eq_mul] at key
    rin

中文:
定理 ConvexOn.secant_mono_aux1
  结论: (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  证明: by
  have hxy' : 0 < y - x := by linarith
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  have ha : 0 <= (z - y) / (z - x) := by positivity
  have hb : 0 <= (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz ha hb ?_
  · simp only [smul_eq_mul] at key
    rin

Depends on / 依赖: linear_combination, ring_nf, smul_eq_mul
-/
theorem ConvexOn.secant_mono_aux1 (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
    (hxy : x < y) (hyz : y < z) : (z - x) * f y <= (z - y) * f x + (y - x) * f z := by
  have hxy' : 0 < y - x := by linarith
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  have ha : 0 <= (z - y) / (z - x) := by positivity
  have hb : 0 <= (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz ha hb ?_
  · simp only [smul_eq_mul] at key
    ring_nf at key
    field_simp at key
    linear_combination key
  · field

/--
theorem `ConvexOn.secant_mono_aux2` / 定理 `ConvexOn.secant_mono_aux2`

English:
theorem ConvexOn.secant_mono_aux2
  statement: (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  proof: by
  have hxy' : 0 < y - x := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_mono_aux1 hx hz hxy hyz]

中文:
定理 ConvexOn.secant_mono_aux2
  结论: (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  证明: by
  have hxy' : 0 < y - x := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_mono_aux1 hx hz hxy hyz]

Depends on / 依赖: hf.secant_mono_aux1, secant_mono_aux1
-/
theorem ConvexOn.secant_mono_aux2 (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
    (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) <= (f z - f x) / (z - x) := by
  have hxy' : 0 < y - x := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_mono_aux1 hx hz hxy hyz]

/--
theorem `ConvexOn.secant_mono_aux3` / 定理 `ConvexOn.secant_mono_aux3`

English:
theorem ConvexOn.secant_mono_aux3
  statement: (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  proof: by
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_mono_aux1 hx hz hxy hyz]

中文:
定理 ConvexOn.secant_mono_aux3
  结论: (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
  证明: by
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_mono_aux1 hx hz hxy hyz]

Depends on / 依赖: hf.secant_mono_aux1, secant_mono_aux1
-/
theorem ConvexOn.secant_mono_aux3 (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s) (hz : z in s)
    (hxy : x < y) (hyz : y < z) : (f z - f x) / (z - x) <= (f z - f y) / (z - y) := by
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_mono_aux1 hx hz hxy hyz]

/--
theorem `ConvexOn.secant_mono` / 定理 `ConvexOn.secant_mono`

English:
theorem ConvexOn.secant_mono
  statement: (hf : ConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a in s) (hx : x in s)
  proof: by
  rcases eq_or_lt_of_le hxy with (rfl | hxy)
  · simp
  rcases lt_or_gt_of_ne hxa with hxa | hxa
  · rcases lt_or_gt_of_ne hya with hya | hya
    · convert! hf.secant_mono_aux3 hx ha hxy hya using 1 <;> rw [← neg_div_neg_eq] <;> simp
    · convert! hf.slope_mono_adjacent hx hy hxa hya using 1
   

中文:
定理 ConvexOn.secant_mono
  结论: (hf : ConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a in s) (hx : x in s)
  证明: by
  rcases eq_or_lt_of_le hxy with (rfl | hxy)
  · simp
  rcases lt_or_gt_of_ne hxa with hxa | hxa
  · rcases lt_or_gt_of_ne hya with hya | hya
    · convert! hf.secant_mono_aux3 hx ha hxy hya using 1 <;> rw [← neg_div_neg_eq] <;> simp
    · convert! hf.slope_mono_adjacent hx hy hxa hya using 1
   

Depends on / 依赖: convert, eq_or_lt_of_le, hf.secant_mono_aux2, hf.secant_mono_aux3, hf.slope_mono_adjacent, lt_or_gt_of_ne, neg_div_neg_eq, secant_mono_aux2, secant_mono_aux3, slope_mono_adjacent
-/
theorem ConvexOn.secant_mono (hf : ConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a in s) (hx : x in s)
    (hy : y in s) (hxa : x != a) (hya : y != a) (hxy : x <= y) :
    (f x - f a) / (x - a) <= (f y - f a) / (y - a) := by
  rcases eq_or_lt_of_le hxy with (rfl | hxy)
  · simp
  rcases lt_or_gt_of_ne hxa with hxa | hxa
  · rcases lt_or_gt_of_ne hya with hya | hya
    · convert! hf.secant_mono_aux3 hx ha hxy hya using 1 <;> rw [← neg_div_neg_eq] <;> simp
    · convert! hf.slope_mono_adjacent hx hy hxa hya using 1
      rw [← neg_div_neg_eq]; simp
  · exact hf.secant_mono_aux2 ha hy hxa hxy

/--
theorem `StrictConvexOn.secant_strict_mono_aux1` / 定理 `StrictConvexOn.secant_strict_mono_aux1`

English:
theorem StrictConvexOn.secant_strict_mono_aux1
  statement: (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
  proof: by
  have hxy' : 0 < y - x := by linarith
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  have ha : 0 < (z - y) / (z - x) := by positivity
  have hb : 0 < (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz (by linarith) ha hb ?_
  · simp only [smul_eq_mul] at

中文:
定理 StrictConvexOn.secant_strict_mono_aux1
  结论: (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
  证明: by
  have hxy' : 0 < y - x := by linarith
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  have ha : 0 < (z - y) / (z - x) := by positivity
  have hb : 0 < (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz (by linarith) ha hb ?_
  · simp only [smul_eq_mul] at

Depends on / 依赖: linear_combination, ring_nf, smul_eq_mul
-/
theorem StrictConvexOn.secant_strict_mono_aux1 (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
    (hz : z in s) (hxy : x < y) (hyz : y < z) : (z - x) * f y < (z - y) * f x + (y - x) * f z := by
  have hxy' : 0 < y - x := by linarith
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  have ha : 0 < (z - y) / (z - x) := by positivity
  have hb : 0 < (y - x) / (z - x) := by positivity
  have key := hf.2 hx hz (by linarith) ha hb ?_
  · simp only [smul_eq_mul] at key
    ring_nf at key
    field_simp at key
    linear_combination key
  · field

/--
theorem `StrictConvexOn.secant_strict_mono_aux2` / 定理 `StrictConvexOn.secant_strict_mono_aux2`

English:
theorem StrictConvexOn.secant_strict_mono_aux2
  statement: (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
  proof: by
  have hxy' : 0 < y - x := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz]

中文:
定理 StrictConvexOn.secant_strict_mono_aux2
  结论: (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
  证明: by
  have hxy' : 0 < y - x := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz]

Depends on / 依赖: hf.secant_strict_mono_aux1, secant_strict_mono_aux1
-/
theorem StrictConvexOn.secant_strict_mono_aux2 (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
    (hz : z in s) (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) < (f z - f x) / (z - x) := by
  have hxy' : 0 < y - x := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz]

/--
theorem `StrictConvexOn.secant_strict_mono_aux3` / 定理 `StrictConvexOn.secant_strict_mono_aux3`

English:
theorem StrictConvexOn.secant_strict_mono_aux3
  statement: (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
  proof: by
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz]

中文:
定理 StrictConvexOn.secant_strict_mono_aux3
  结论: (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
  证明: by
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz]

Depends on / 依赖: hf.secant_strict_mono_aux1, secant_strict_mono_aux1
-/
theorem StrictConvexOn.secant_strict_mono_aux3 (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x in s)
    (hz : z in s) (hxy : x < y) (hyz : y < z) : (f z - f x) / (z - x) < (f z - f y) / (z - y) := by
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  field_simp
  linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz]

/--
theorem `StrictConvexOn.secant_strict_mono` / 定理 `StrictConvexOn.secant_strict_mono`

English:
theorem StrictConvexOn.secant_strict_mono
  statement: (hf : StrictConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a in s)
  proof: by
  rcases lt_or_gt_of_ne hxa with hxa | hxa
  · rcases lt_or_gt_of_ne hya with hya | hya
    · convert! hf.secant_strict_mono_aux3 hx ha hxy hya using 1 <;> rw [← neg_div_neg_eq] <;>
        simp
    · convert! hf.slope_strict_mono_adjacent hx hy hxa hya using 1
      rw [← neg_div_neg_eq]; simp
 

中文:
定理 StrictConvexOn.secant_strict_mono
  结论: (hf : StrictConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a in s)
  证明: by
  rcases lt_or_gt_of_ne hxa with hxa | hxa
  · rcases lt_or_gt_of_ne hya with hya | hya
    · convert! hf.secant_strict_mono_aux3 hx ha hxy hya using 1 <;> rw [← neg_div_neg_eq] <;>
        simp
    · convert! hf.slope_strict_mono_adjacent hx hy hxa hya using 1
      rw [← neg_div_neg_eq]; simp
 

Depends on / 依赖: convert, hf.secant_strict_mono_aux2, hf.secant_strict_mono_aux3, hf.slope_strict_mono_adjacent, lt_or_gt_of_ne, neg_div_neg_eq, secant_strict_mono_aux2, secant_strict_mono_aux3, slope_strict_mono_adjacent
-/
theorem StrictConvexOn.secant_strict_mono (hf : StrictConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a in s)
    (hx : x in s) (hy : y in s) (hxa : x != a) (hya : y != a) (hxy : x < y) :
    (f x - f a) / (x - a) < (f y - f a) / (y - a) := by
  rcases lt_or_gt_of_ne hxa with hxa | hxa
  · rcases lt_or_gt_of_ne hya with hya | hya
    · convert! hf.secant_strict_mono_aux3 hx ha hxy hya using 1 <;> rw [← neg_div_neg_eq] <;>
        simp
    · convert! hf.slope_strict_mono_adjacent hx hy hxa hya using 1
      rw [← neg_div_neg_eq]; simp
  · exact hf.secant_strict_mono_aux2 ha hy hxa hxy

/--
theorem `StrictConcaveOn.secant_strict_mono` / 定理 `StrictConcaveOn.secant_strict_mono`

English:
theorem StrictConcaveOn.secant_strict_mono
  statement: (hf : StrictConcaveOn 𝕜 s f) {a x y : 𝕜} (ha : a in s)
  proof: by
  have key := hf.neg.secant_strict_mono ha hx hy hxa hya hxy
  simp only [Pi.neg_apply] at key
  linear_combination key

中文:
定理 StrictConcaveOn.secant_strict_mono
  结论: (hf : StrictConcaveOn 𝕜 s f) {a x y : 𝕜} (ha : a in s)
  证明: by
  have key := hf.neg.secant_strict_mono ha hx hy hxa hya hxy
  simp only [Pi.neg_apply] at key
  linear_combination key

Depends on / 依赖: Pi.neg_apply, hf.neg.secant_strict_mono, linear_combination, neg_apply, secant_strict_mono
-/
theorem StrictConcaveOn.secant_strict_mono (hf : StrictConcaveOn 𝕜 s f) {a x y : 𝕜} (ha : a in s)
    (hx : x in s) (hy : y in s) (hxa : x != a) (hya : y != a) (hxy : x < y) :
    (f y - f a) / (y - a) < (f x - f a) / (x - a) := by
  have key := hf.neg.secant_strict_mono ha hx hy hxa hya hxy
  simp only [Pi.neg_apply] at key
  linear_combination key

/--
theorem `ConvexOn.strictMonoOn` / 定理 `ConvexOn.strictMonoOn`

English:
theorem ConvexOn.strictMonoOn
  statement: (hf : ConvexOn 𝕜 s f) {x y : 𝕜} (hx : x in s) (hxy : x < y)
  proof: by
  intro u hu v hv huv
  have step1 : forall {z : 𝕜}, z in s inter Set.Ioi y -> f y < f z := by
    intro z hz
    refine hf.lt_right_of_left_lt hx hz.1 ?_ hxy'
    rw [openSegment_eq_Ioo (hxy.trans hz.2)]
    exact ⟨hxy, hz.2⟩
  rcases eq_or_lt_of_le hu.2 with (rfl | hu2)
  · exact step1 ⟨hv.1, h

中文:
定理 ConvexOn.strictMonoOn
  结论: (hf : ConvexOn 𝕜 s f) {x y : 𝕜} (hx : x in s) (hxy : x < y)
  证明: by
  intro u hu v hv huv
  have step1 : forall {z : 𝕜}, z in s inter Set.Ioi y -> f y < f z := by
    intro z hz
    refine hf.lt_right_of_left_lt hx hz.1 ?_ hxy'
    rw [openSegment_eq_Ioo (hxy.trans hz.2)]
    exact ⟨hxy, hz.2⟩
  rcases eq_or_lt_of_le hu.2 with (rfl | hu2)
  · exact step1 ⟨hv.1, h

Depends on / 依赖: Set.Ioi, eq_or_lt_of_le, hf.lt_right_of_left_lt, hu2.trans, hxy.le, hxy.le.trans, hxy.trans, lt_right_of_left_lt, openSegment_eq_Ioo, segment_eq_Icc, segment_subset
-/
theorem ConvexOn.strictMonoOn (hf : ConvexOn 𝕜 s f) {x y : 𝕜} (hx : x in s) (hxy : x < y)
    (hxy' : f x < f y) : StrictMonoOn f (s inter Set.Ici y) := by
  intro u hu v hv huv
  have step1 : forall {z : 𝕜}, z in s inter Set.Ioi y -> f y < f z := by
    intro z hz
    refine hf.lt_right_of_left_lt hx hz.1 ?_ hxy'
    rw [openSegment_eq_Ioo (hxy.trans hz.2)]
    exact ⟨hxy, hz.2⟩
  rcases eq_or_lt_of_le hu.2 with (rfl | hu2)
  · exact step1 ⟨hv.1, huv⟩
  · refine hf.lt_right_of_left_lt ?_ hv.1 ?_ (step1 ⟨hu.1, hu2⟩)
    · apply hf.1.segment_subset hx hu.1
      rw [segment_eq_Icc (hxy.le.trans hu.2)]
      exact ⟨hxy.le, hu.2⟩
    · rw [openSegment_eq_Ioo (hu2.trans huv)]
      exact ⟨hu2, huv⟩

/--
theorem `ConvexOn.strictAntiOn` / 定理 `ConvexOn.strictAntiOn`

English:
theorem ConvexOn.strictAntiOn
  statement: (hf : ConvexOn 𝕜 s f) {x y : 𝕜} (hy : y in s) (hxy : x < y)
  proof: by
.strictMonoOn (by simpa) (neg_lt_neg hxy) (by simpa) have := hf.comp_affineMap (-.id ..)
  simpa [Function.comp_def] using this.comp_strictAntiOn strictMonoOn_id.neg fun _ _ => by simpa

中文:
定理 ConvexOn.strictAntiOn
  结论: (hf : ConvexOn 𝕜 s f) {x y : 𝕜} (hy : y in s) (hxy : x < y)
  证明: by
.strictMonoOn (by simpa) (neg_lt_neg hxy) (by simpa) have := hf.comp_affineMap (-.id ..)
  simpa [Function.comp_def] using this.comp_strictAntiOn strictMonoOn_id.neg fun _ _ => by simpa

Depends on / 依赖: Function, Function.comp_def, comp_affineMap, comp_def, comp_strictAntiOn, hf.comp_affineMap, neg_lt_neg, strictMonoOn, strictMonoOn_id, strictMonoOn_id.neg, this.comp_strictAntiOn
-/
theorem ConvexOn.strictAntiOn (hf : ConvexOn 𝕜 s f) {x y : 𝕜} (hy : y in s) (hxy : x < y)
    (hxy' : f y < f x) : StrictAntiOn f (s inter .Iic x) := by
.strictMonoOn (by simpa) (neg_lt_neg hxy) (by simpa) have := hf.comp_affineMap (-.id ..)
  simpa [Function.comp_def] using this.comp_strictAntiOn strictMonoOn_id.neg fun _ _ => by simpa

/--
theorem `ConcaveOn.strictMonoOn` / 定理 `ConcaveOn.strictMonoOn`

English:
theorem ConcaveOn.strictMonoOn
  statement: (hf : ConcaveOn 𝕜 s f) {x y : 𝕜} (hy : y in s) (hxy : x < y)
  proof: by
  simpa using (neg_convexOn_iff.mpr hf |>.strictAntiOn hy hxy <| neg_lt_neg hxy').neg

中文:
定理 ConcaveOn.strictMonoOn
  结论: (hf : ConcaveOn 𝕜 s f) {x y : 𝕜} (hy : y in s) (hxy : x < y)
  证明: by
  simpa using (neg_convexOn_iff.mpr hf |>.strictAntiOn hy hxy <| neg_lt_neg hxy').neg

Depends on / 依赖: neg_convexOn_iff, neg_convexOn_iff.mpr, neg_lt_neg, strictAntiOn
-/
theorem ConcaveOn.strictMonoOn (hf : ConcaveOn 𝕜 s f) {x y : 𝕜} (hy : y in s) (hxy : x < y)
    (hxy' : f x < f y) : StrictMonoOn f (s inter .Iic x) := by
  simpa using (neg_convexOn_iff.mpr hf |>.strictAntiOn hy hxy <| neg_lt_neg hxy').neg

/--
theorem `ConcaveOn.strictAntiOn` / 定理 `ConcaveOn.strictAntiOn`

English:
theorem ConcaveOn.strictAntiOn
  statement: (hf : ConcaveOn 𝕜 s f) {x y : 𝕜} (hx : x in s) (hxy : x < y)
  proof: by
  simpa using (neg_convexOn_iff.mpr hf |>.strictMonoOn hx hxy <| neg_lt_neg hxy').neg

中文:
定理 ConcaveOn.strictAntiOn
  结论: (hf : ConcaveOn 𝕜 s f) {x y : 𝕜} (hx : x in s) (hxy : x < y)
  证明: by
  simpa using (neg_convexOn_iff.mpr hf |>.strictMonoOn hx hxy <| neg_lt_neg hxy').neg

Depends on / 依赖: neg_convexOn_iff, neg_convexOn_iff.mpr, neg_lt_neg, strictMonoOn
-/
theorem ConcaveOn.strictAntiOn (hf : ConcaveOn 𝕜 s f) {x y : 𝕜} (hx : x in s) (hxy : x < y)
    (hxy' : f y < f x) : StrictAntiOn f (s inter .Ici y) := by
  simpa using (neg_convexOn_iff.mpr hf |>.strictMonoOn hx hxy <| neg_lt_neg hxy').neg
