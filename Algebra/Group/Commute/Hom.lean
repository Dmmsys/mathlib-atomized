/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Multiplicative homomorphisms respect semiconjugation and commutation.
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

section Commute

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

@[to_additive (attr := simp)]
/--
theorem `SemiconjBy.map` / 定理 `SemiconjBy.map`

English:
theorem SemiconjBy.map
  given: [MulHomClass F M N] (h : SemiconjBy a x y) (f : F)
  proof: by simpa only [SemiconjBy, map_mul] using congr_arg f h

@[to_additive (attr := simp)]

中文:
定理 SemiconjBy.map
  条件: [乘法态射类 F M N] (h : SemiconjBy a x y) (f : F)
  证明: by simpa only [SemiconjBy, map_mul] using congr_arg f h

@[to_additive (attr := simp)]
-/
protected theorem SemiconjBy.map [MulHomClass F M N] (h : SemiconjBy a x y) (f : F) :
    SemiconjBy (f a) (f x) (f y) := by simpa only [SemiconjBy, map_mul] using congr_arg f h

@[to_additive (attr := simp)]
/--
theorem `Commute.map` / 定理 `Commute.map`

English:
theorem Commute.map
  given: [MulHomClass F M N] (h : Commute x y) (f : F)
  statement: Commute (f x) (f y)
  proof: SemiconjBy.map h f

@[to_additive]

中文:
定理 Commute.map
  条件: [乘法态射类 F M N] (h : Commute x y) (f : F)
  结论: Commute (f x) (f y)
  证明: SemiconjBy.map h f

@[to_additive]
-/
protected theorem Commute.map [MulHomClass F M N] (h : Commute x y) (f : F) : Commute (f x) (f y) :=
  SemiconjBy.map h f

@[to_additive]
/--
theorem `SemiconjBy.of_map` / 定理 `SemiconjBy.of_map`

English:
theorem SemiconjBy.of_map
  statement: [MulHomClass F M N] {f : F} (hf : Function.Injective f)
  proof: hf (by simpa only [SemiconjBy, map_mul] using h)

@[to_additive]

中文:
定理 SemiconjBy.of_map
  结论: [乘法态射类 F M N] {f : F} (hf : 函数.单射 f)
  证明: hf (by simpa only [SemiconjBy, map_mul] using h)

@[to_additive]
-/
protected theorem SemiconjBy.of_map [MulHomClass F M N] {f : F} (hf : Function.Injective f)
    (h : SemiconjBy (f a) (f x) (f y)) : SemiconjBy a x y :=
  hf (by simpa only [SemiconjBy, map_mul] using h)

@[to_additive]
/--
theorem `Commute.of_map` / 定理 `Commute.of_map`

English:
theorem Commute.of_map
  statement: [MulHomClass F M N] {f : F} (hf : Function.Injective f)
  proof: hf (by simpa only [map_mul] using h.eq)

@[to_additive]

中文:
定理 Commute.of_map
  结论: [乘法态射类 F M N] {f : F} (hf : 函数.单射 f)
  证明: hf (by simpa only [map_mul] using h.eq)

@[to_additive]

Depends on / 依赖: h.eq, map_mul
-/
theorem Commute.of_map [MulHomClass F M N] {f : F} (hf : Function.Injective f)
    (h : Commute (f x) (f y)) : Commute x y :=
  hf (by simpa only [map_mul] using h.eq)

@[to_additive]
/--
theorem `semiconjBy_map_iff` / 定理 `semiconjBy_map_iff`

English:
theorem semiconjBy_map_iff
  given: [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y : M}
  proof: ⟨.of_map hf, (.map · f)⟩

@[to_additive]

中文:
定理 semiconjBy_map_iff
  条件: [乘法态射类 F M N] {f : F} (hf : 函数.单射 f) {x y : M}
  证明: ⟨.of_map hf, (.map · f)⟩

@[to_additive]

Depends on / 依赖: of_map
-/
theorem semiconjBy_map_iff [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y : M} :
    SemiconjBy (f a) (f x) (f y) ↔ SemiconjBy a x y :=
  ⟨.of_map hf, (.map · f)⟩

@[to_additive]
/--
theorem `commute_map_iff` / 定理 `commute_map_iff`

English:
theorem commute_map_iff
  given: [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y : M}
  proof: ⟨.of_map hf, (.map · f)⟩

中文:
定理 commute_map_iff
  条件: [乘法态射类 F M N] {f : F} (hf : 函数.单射 f) {x y : M}
  证明: ⟨.of_map hf, (.map · f)⟩

Depends on / 依赖: of_map
-/
theorem commute_map_iff [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y : M} :
    Commute (f x) (f y) ↔ Commute x y :=
  ⟨.of_map hf, (.map · f)⟩

end Commute
