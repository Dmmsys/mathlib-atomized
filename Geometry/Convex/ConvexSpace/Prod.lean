/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Product of convex spaces

This file defines the cartesian product of convex spaces.
-/

open Convexity Finsupp Set

public noncomputable section

variable {I R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

namespace Prod
variable {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]

/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConvexSpace R (X × Y) := .mk
  (fun w ↦ (w.iConvexComb fst, w.iConvexComb snd))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
/-
**Prod.fst_sConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：fst_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.fst = w.iConvex
Comb fst
参数：w : StdSimplex R (X × Y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.fst = w.iConvexComb fst := rfl

@[simp]
/-
**Prod.snd_sConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：snd_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.snd = w.iConvex
Comb snd
参数：w : StdSimplex R (X × Y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.snd = w.iConvexComb snd := rfl

@[fun_prop]
/-
**Prod.isAffineMap_fst** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：isAffineMap_fst : IsAffineMap R (fst : X × Y -> X) where map_sConvexComb
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Prod.fst_sConvexComb`：fst_sConvexComb (w : StdSimplex R (X × Y)) : w.sCo
nvexComb.fst = w.iConvexComb fst
-/
lemma isAffineMap_fst : IsAffineMap R (fst : X × Y → X) where map_sConvexComb := fst_sConvexComb

@[fun_prop]
/-
**Prod.isAffineMap_snd** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：isAffineMap_snd : IsAffineMap R (snd : X × Y -> Y) where map_sConvexComb
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Prod.snd_sConvexComb`：snd_sConvexComb (w : StdSimplex R (X × Y)) : w.sCo
nvexComb.snd = w.iConvexComb snd
-/
lemma isAffineMap_snd : IsAffineMap R (snd : X × Y → Y) where map_sConvexComb := snd_sConvexComb

@[simp]
/-
**Prod.fst_iConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：fst_iConvexComb (w : StdSimplex R I) (f : I -> X × Y) : (w.iConvexComb f).
fst = w.iConvexComb (fun i => (f i).fst)
参数：w : StdSimplex R I；f : I -> X × Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_iConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [in
st_2 : IsStrictOrderedRing …
· 使用引理 `Prod.isAffineMap_fst`：isAffineMap_fst : IsAffineMap R (fst : X × Y -> X)
 where map_sConvexComb
-/
lemma fst_iConvexComb (w : StdSimplex R I) (f : I → X × Y) :
    (w.iConvexComb f).fst = w.iConvexComb (fun i ↦ (f i).fst) :=
  isAffineMap_fst.map_iConvexComb ..

@[simp]
/-
**Prod.snd_iConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：snd_iConvexComb (w : StdSimplex R I) (f : I -> X × Y) : (w.iConvexComb f).
snd = w.iConvexComb (fun i => (f i).snd)
参数：w : StdSimplex R I；f : I -> X × Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_iConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [in
st_2 : IsStrictOrderedRing …
· 使用引理 `Prod.isAffineMap_snd`：isAffineMap_snd : IsAffineMap R (snd : X × Y -> Y)
 where map_sConvexComb
-/
lemma snd_iConvexComb (w : StdSimplex R I) (f : I → X × Y) :
    (w.iConvexComb f).snd = w.iConvexComb (fun i ↦ (f i).snd) :=
  isAffineMap_snd.map_iConvexComb ..

@[simp]
/-
**Prod.fst_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：fst_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) : (convexCombPair a
 b ha hb hab x y).fst = convexCombPair a b ha hb hab x.fst y.fst
参数：a b : R；ha hb hab；x y : X × Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_convexCombPair`：∀ {R : Type u_1} {M : Type u_3
} {N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing R] [inst_3 : Co…
· 使用引理 `Prod.isAffineMap_fst`：isAffineMap_fst : IsAffineMap R (fst : X × Y -> X)
 where map_sConvexComb
-/
lemma fst_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) :
    (convexCombPair a b ha hb hab x y).fst = convexCombPair a b ha hb hab x.fst y.fst :=
  isAffineMap_fst.map_convexCombPair ..

@[simp]
/-
**Prod.snd_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：snd_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) : (convexCombPair a
 b ha hb hab x y).snd = convexCombPair a b ha hb hab x.snd y.snd
参数：a b : R；ha hb hab；x y : X × Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_convexCombPair`：∀ {R : Type u_1} {M : Type u_3
} {N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing R] [inst_3 : Co…
· 使用引理 `Prod.isAffineMap_snd`：isAffineMap_snd : IsAffineMap R (snd : X × Y -> Y)
 where map_sConvexComb
-/
lemma snd_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) :
    (convexCombPair a b ha hb hab x y).snd = convexCombPair a b ha hb hab x.snd y.snd :=
  isAffineMap_snd.map_convexCombPair ..

end Prod

namespace Pi
variable {ι : Type*} {X : ι → Type*} [∀ i, ConvexSpace R (X i)] {i : ι}

/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConvexSpace R (∀ i, X i) := .mk
  (fun w i ↦ w.iConvexComb (· i))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
/-
**Pi.sConvexComb_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：sConvexComb_apply (w : StdSimplex R (forall i, X i)) (i : ι) : w.sConvexCo
mb i = w.iConvexComb (· i)
参数：w : StdSimplex R (forall i, X i)；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sConvexComb_apply (w : StdSimplex R (∀ i, X i)) (i : ι) :
    w.sConvexComb i = w.iConvexComb (· i) := rfl

@[fun_prop]
/-
**Pi.isAffineMap_eval** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：isAffineMap_eval : IsAffineMap R (· i : (forall i, X i) -> X i) where map_
sConvexComb _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.sConvexComb_apply`：sConvexComb_apply (w : StdSimplex R (forall i, X i
)) (i : ι) : w.sConvexComb i = w.iConvexComb (· i)
-/
lemma isAffineMap_eval : IsAffineMap R (· i : (∀ i, X i) → X i) where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
/-
**Pi.iConvexComb_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：iConvexComb_apply (w : StdSimplex R I) (f : I -> forall i, X i) (i : ι) : 
w.iConvexComb f i = w.iConvexComb (fun j => f j i)
参数：w : StdSimplex R I；f : I -> forall i, X i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_iConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [in
st_2 : IsStrictOrderedRing …
· 使用引理 `Pi.isAffineMap_eval`：isAffineMap_eval : IsAffineMap R (· i : (forall i, 
X i) -> X i) where map_sConvexComb _
-/
lemma iConvexComb_apply (w : StdSimplex R I) (f : I → ∀ i, X i) (i : ι) :
    w.iConvexComb f i = w.iConvexComb (fun j ↦ f j i) := isAffineMap_eval.map_iConvexComb ..

@[simp]
/-
**Pi.convexCombPair_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：convexCombPair_apply (a b : R) (ha hb hab) (f g : forall i, X i) (i : ι) :
 convexCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i)
参数：a b : R；ha hb hab；f g : forall i, X i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_convexCombPair`：∀ {R : Type u_1} {M : Type u_3
} {N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing R] [inst_3 : Co…
· 使用引理 `Pi.isAffineMap_eval`：isAffineMap_eval : IsAffineMap R (· i : (forall i, 
X i) -> X i) where map_sConvexComb _
-/
lemma convexCombPair_apply (a b : R) (ha hb hab) (f g : ∀ i, X i) (i : ι) :
    convexCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i) :=
  isAffineMap_eval.map_convexCombPair ..

end Pi

namespace Finsupp
variable {ι : Type*} {X : Type*} [Zero X] [ConvexSpace R X] {i : ι}

/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConvexSpace R (ι →₀ X) := .mk
  (fun w ↦ by
    classical
    refine .onFinset (w.weights.support.biUnion Finsupp.support) (fun i ↦ w.iConvexComb (· i)) ?_
    rintro i hi
    contrapose! hi
    simp_all)
  (by simp)
  (fun w ↦ by ext; simp [iConvexComb_assoc])

@[simp]
/-
**Finsupp.sConvexComb_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sConvexComb_apply (w : StdSimplex R (ι ->₀ X)) (i : ι) : w.sConvexComb i =
 w.iConvexComb (· i)
参数：w : StdSimplex R (ι ->₀ X)；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sConvexComb_apply (w : StdSimplex R (ι →₀ X)) (i : ι) :
    w.sConvexComb i = w.iConvexComb (· i) := rfl

@[fun_prop]
/-
**Finsupp.isAffineMap_eval** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：isAffineMap_eval : IsAffineMap R (· i : (ι ->₀ X) -> X) where map_sConvexC
omb _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.sConvexComb_apply`：sConvexComb_apply (w : StdSimplex R (ι ->₀ X)
) (i : ι) : w.sConvexComb i = w.iConvexComb (· i)
-/
lemma isAffineMap_eval : IsAffineMap R (· i : (ι →₀ X) → X) where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
/-
**Finsupp.iConvexComb_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：iConvexComb_apply (w : StdSimplex R I) (f : I -> ι ->₀ X) (i : ι) : w.iCon
vexComb f i = w.iConvexComb (fun j => f j i)
参数：w : StdSimplex R I；f : I -> ι ->₀ X；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_iConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [in
st_2 : IsStrictOrderedRing …
· 使用引理 `Finsupp.isAffineMap_eval`：isAffineMap_eval : IsAffineMap R (· i : (ι ->₀
 X) -> X) where map_sConvexComb _
-/
lemma iConvexComb_apply (w : StdSimplex R I) (f : I → ι →₀ X) (i : ι) :
    w.iConvexComb f i = w.iConvexComb (fun j ↦ f j i) := isAffineMap_eval.map_iConvexComb ..

@[simp]
/-
**Finsupp.convexCombPair_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：convexCombPair_apply (a b : R) (ha hb hab) (f g : ι ->₀ X) (i : ι) : conve
xCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i)
参数：a b : R；ha hb hab；f g : ι ->₀ X；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_convexCombPair`：∀ {R : Type u_1} {M : Type u_3
} {N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing R] [inst_3 : Co…
· 使用引理 `Finsupp.isAffineMap_eval`：isAffineMap_eval : IsAffineMap R (· i : (ι ->₀
 X) -> X) where map_sConvexComb _
-/
lemma convexCombPair_apply (a b : R) (ha hb hab) (f g : ι →₀ X) (i : ι) :
    convexCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i) :=
  isAffineMap_eval.map_convexCombPair ..

end Finsupp

