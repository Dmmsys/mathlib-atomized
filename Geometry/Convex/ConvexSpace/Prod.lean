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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConvexSpace R (X × Y)
  body: .mk
  (fun w => (w.iConvexComb fst, w.iConvexComb snd))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]

中文:
实例 :
  签名: 凸空间 R (X × Y)
  定义体: .mk
  (fun w => (w.iConvexComb fst, w.iConvexComb snd))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
-/
instance : ConvexSpace R (X × Y) := .mk
  (fun w => (w.iConvexComb fst, w.iConvexComb snd))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
/--
lemma `fst_sConvexComb` / 引理 `fst_sConvexComb`

English:
lemma fst_sConvexComb
  given: (w : StdSimplex R (X × Y))
  statement: w.sConvexComb.fst = w.iConvexComb fst
  proof: rfl

@[simp]

中文:
引理 fst_sConvexComb
  条件: (w : 标准单纯形 R (X × Y))
  结论: w.sConvexComb.fst = w.iConvexComb fst
  证明: rfl

@[simp]
-/
lemma fst_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.fst = w.iConvexComb fst := rfl

@[simp]
/--
lemma `snd_sConvexComb` / 引理 `snd_sConvexComb`

English:
lemma snd_sConvexComb
  given: (w : StdSimplex R (X × Y))
  statement: w.sConvexComb.snd = w.iConvexComb snd
  proof: rfl

@[fun_prop]

中文:
引理 snd_sConvexComb
  条件: (w : 标准单纯形 R (X × Y))
  结论: w.sConvexComb.snd = w.iConvexComb snd
  证明: rfl

@[fun_prop]
-/
lemma snd_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.snd = w.iConvexComb snd := rfl

@[fun_prop]
/--
lemma `isAffineMap_fst` / 引理 `isAffineMap_fst`

English:
lemma isAffineMap_fst
  statement: IsAffineMap R (fst : X × Y -> X) where map_sConvexComb
  proof: fst_sConvexComb

@[fun_prop]

中文:
引理 isAffineMap_fst
  结论: 是仿射映射 R (fst : X × Y -> X) where map_sConvexComb
  证明: fst_sConvexComb

@[fun_prop]

Depends on / 依赖: fst_sConvexComb
-/
lemma isAffineMap_fst : IsAffineMap R (fst : X × Y -> X) where map_sConvexComb := fst_sConvexComb

@[fun_prop]
/--
lemma `isAffineMap_snd` / 引理 `isAffineMap_snd`

English:
lemma isAffineMap_snd
  statement: IsAffineMap R (snd : X × Y -> Y) where map_sConvexComb
  proof: snd_sConvexComb

@[simp]

中文:
引理 isAffineMap_snd
  结论: 是仿射映射 R (snd : X × Y -> Y) where map_sConvexComb
  证明: snd_sConvexComb

@[simp]

Depends on / 依赖: snd_sConvexComb
-/
lemma isAffineMap_snd : IsAffineMap R (snd : X × Y -> Y) where map_sConvexComb := snd_sConvexComb

@[simp]
/--
lemma `fst_iConvexComb` / 引理 `fst_iConvexComb`

English:
lemma fst_iConvexComb
  given: (w : StdSimplex R I) (f : I -> X × Y)
  proof: isAffineMap_fst.map_iConvexComb ..

@[simp]

中文:
引理 fst_iConvexComb
  条件: (w : 标准单纯形 R I) (f : I -> X × Y)
  证明: isAffineMap_fst.map_iConvexComb ..

@[simp]

Depends on / 依赖: isAffineMap_fst, isAffineMap_fst.map_iConvexComb, map_iConvexComb
-/
lemma fst_iConvexComb (w : StdSimplex R I) (f : I -> X × Y) :
    (w.iConvexComb f).fst = w.iConvexComb (fun i => (f i).fst) :=
  isAffineMap_fst.map_iConvexComb ..

@[simp]
/--
lemma `snd_iConvexComb` / 引理 `snd_iConvexComb`

English:
lemma snd_iConvexComb
  given: (w : StdSimplex R I) (f : I -> X × Y)
  proof: isAffineMap_snd.map_iConvexComb ..

@[simp]

中文:
引理 snd_iConvexComb
  条件: (w : 标准单纯形 R I) (f : I -> X × Y)
  证明: isAffineMap_snd.map_iConvexComb ..

@[simp]

Depends on / 依赖: isAffineMap_snd, isAffineMap_snd.map_iConvexComb, map_iConvexComb
-/
lemma snd_iConvexComb (w : StdSimplex R I) (f : I -> X × Y) :
    (w.iConvexComb f).snd = w.iConvexComb (fun i => (f i).snd) :=
  isAffineMap_snd.map_iConvexComb ..

@[simp]
/--
lemma `fst_convexCombPair` / 引理 `fst_convexCombPair`

English:
lemma fst_convexCombPair
  given: (a b : R) (ha hb hab) (x y : X × Y)
  proof: isAffineMap_fst.map_convexCombPair ..

@[simp]

中文:
引理 fst_convexCombPair
  条件: (a b : R) (ha hb hab) (x y : X × Y)
  证明: isAffineMap_fst.map_convexCombPair ..

@[simp]

Depends on / 依赖: isAffineMap_fst, isAffineMap_fst.map_convexCombPair, map_convexCombPair
-/
lemma fst_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) :
    (convexCombPair a b ha hb hab x y).fst = convexCombPair a b ha hb hab x.fst y.fst :=
  isAffineMap_fst.map_convexCombPair ..

@[simp]
/--
lemma `snd_convexCombPair` / 引理 `snd_convexCombPair`

English:
lemma snd_convexCombPair
  given: (a b : R) (ha hb hab) (x y : X × Y)
  proof: isAffineMap_snd.map_convexCombPair ..

中文:
引理 snd_convexCombPair
  条件: (a b : R) (ha hb hab) (x y : X × Y)
  证明: isAffineMap_snd.map_convexCombPair ..

Depends on / 依赖: isAffineMap_snd, isAffineMap_snd.map_convexCombPair, map_convexCombPair
-/
lemma snd_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) :
    (convexCombPair a b ha hb hab x y).snd = convexCombPair a b ha hb hab x.snd y.snd :=
  isAffineMap_snd.map_convexCombPair ..

end Prod

namespace Pi
variable {ι : Type*} {X : ι -> Type*} [forall i, ConvexSpace R (X i)] {i : ι}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConvexSpace R (forall i, X i)
  body: .mk
  (fun w i => w.iConvexComb (· i))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]

中文:
实例 :
  签名: 凸空间 R (对任意 i, X i)
  定义体: .mk
  (fun w i => w.iConvexComb (· i))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
-/
instance : ConvexSpace R (forall i, X i) := .mk
  (fun w i => w.iConvexComb (· i))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
/--
lemma `sConvexComb_apply` / 引理 `sConvexComb_apply`

English:
lemma sConvexComb_apply
  given: (w : StdSimplex R (forall i, X i)) (i : ι)
  proof: rfl

@[fun_prop]

中文:
引理 sConvexComb_apply
  条件: (w : 标准单纯形 R (对任意 i, X i)) (i : ι)
  证明: rfl

@[fun_prop]
-/
lemma sConvexComb_apply (w : StdSimplex R (forall i, X i)) (i : ι) :
    w.sConvexComb i = w.iConvexComb (· i) := rfl

@[fun_prop]
/--
lemma `isAffineMap_eval` / 引理 `isAffineMap_eval`

English:
lemma isAffineMap_eval
  statement: IsAffineMap R (· i : (forall i, X i) -> X i) where
  proof: sConvexComb_apply ..

@[simp]

中文:
引理 isAffineMap_eval
  结论: 是仿射映射 R (· i : (对任意 i, X i) -> X i) where
  证明: sConvexComb_apply ..

@[simp]

Depends on / 依赖: sConvexComb_apply
-/
lemma isAffineMap_eval : IsAffineMap R (· i : (forall i, X i) -> X i) where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
/--
lemma `iConvexComb_apply` / 引理 `iConvexComb_apply`

English:
lemma iConvexComb_apply
  given: (w : StdSimplex R I) (f : I -> forall i, X i) (i : ι)
  proof: isAffineMap_eval.map_iConvexComb ..

@[simp]

中文:
引理 iConvexComb_apply
  条件: (w : 标准单纯形 R I) (f : I -> 对任意 i, X i) (i : ι)
  证明: isAffineMap_eval.map_iConvexComb ..

@[simp]

Depends on / 依赖: isAffineMap_eval, isAffineMap_eval.map_iConvexComb, map_iConvexComb
-/
lemma iConvexComb_apply (w : StdSimplex R I) (f : I -> forall i, X i) (i : ι) :
    w.iConvexComb f i = w.iConvexComb (fun j => f j i) := isAffineMap_eval.map_iConvexComb ..

@[simp]
/--
lemma `convexCombPair_apply` / 引理 `convexCombPair_apply`

English:
lemma convexCombPair_apply
  given: (a b : R) (ha hb hab) (f g : forall i, X i) (i : ι)
  proof: isAffineMap_eval.map_convexCombPair ..

中文:
引理 convexCombPair_apply
  条件: (a b : R) (ha hb hab) (f g : 对任意 i, X i) (i : ι)
  证明: isAffineMap_eval.map_convexCombPair ..

Depends on / 依赖: isAffineMap_eval, isAffineMap_eval.map_convexCombPair, map_convexCombPair
-/
lemma convexCombPair_apply (a b : R) (ha hb hab) (f g : forall i, X i) (i : ι) :
    convexCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i) :=
  isAffineMap_eval.map_convexCombPair ..

end Pi

namespace Finsupp
variable {ι : Type*} {X : Type*} [Zero X] [ConvexSpace R X] {i : ι}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConvexSpace R (ι ->₀ X)
  body: .mk
  (fun w => by
    classical
    refine .onFinset (w.weights.support.biUnion Finsupp.support) (fun i => w.iConvexComb (· i)) ?_
    rintro i hi
    contrapose! hi
    simp_all)
  (by simp)
  (fun w => by ext; simp [iConvexComb_assoc])

@[simp]

中文:
实例 :
  签名: 凸空间 R (ι ->₀ X)
  定义体: .mk
  (fun w => by
    classical
    refine .onFinset (w.weights.support.biUnion Finsupp.support) (fun i => w.iConvexComb (· i)) ?_
    rintro i hi
    contrapose! hi
    simp_all)
  (by simp)
  (fun w => by ext; simp [iConvexComb_assoc])

@[simp]
-/
instance : ConvexSpace R (ι ->₀ X) := .mk
  (fun w => by
    classical
    refine .onFinset (w.weights.support.biUnion Finsupp.support) (fun i => w.iConvexComb (· i)) ?_
    rintro i hi
    contrapose! hi
    simp_all)
  (by simp)
  (fun w => by ext; simp [iConvexComb_assoc])

@[simp]
/--
lemma `sConvexComb_apply` / 引理 `sConvexComb_apply`

English:
lemma sConvexComb_apply
  given: (w : StdSimplex R (ι ->₀ X)) (i : ι)
  proof: rfl

@[fun_prop]

中文:
引理 sConvexComb_apply
  条件: (w : 标准单纯形 R (ι ->₀ X)) (i : ι)
  证明: rfl

@[fun_prop]
-/
lemma sConvexComb_apply (w : StdSimplex R (ι ->₀ X)) (i : ι) :
    w.sConvexComb i = w.iConvexComb (· i) := rfl

@[fun_prop]
/--
lemma `isAffineMap_eval` / 引理 `isAffineMap_eval`

English:
lemma isAffineMap_eval
  statement: IsAffineMap R (· i : (ι ->₀ X) -> X) where
  proof: sConvexComb_apply ..

@[simp]

中文:
引理 isAffineMap_eval
  结论: 是仿射映射 R (· i : (ι ->₀ X) -> X) where
  证明: sConvexComb_apply ..

@[simp]

Depends on / 依赖: sConvexComb_apply
-/
lemma isAffineMap_eval : IsAffineMap R (· i : (ι ->₀ X) -> X) where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
/--
lemma `iConvexComb_apply` / 引理 `iConvexComb_apply`

English:
lemma iConvexComb_apply
  given: (w : StdSimplex R I) (f : I -> ι ->₀ X) (i : ι)
  proof: isAffineMap_eval.map_iConvexComb ..

@[simp]

中文:
引理 iConvexComb_apply
  条件: (w : 标准单纯形 R I) (f : I -> ι ->₀ X) (i : ι)
  证明: isAffineMap_eval.map_iConvexComb ..

@[simp]

Depends on / 依赖: isAffineMap_eval, isAffineMap_eval.map_iConvexComb, map_iConvexComb
-/
lemma iConvexComb_apply (w : StdSimplex R I) (f : I -> ι ->₀ X) (i : ι) :
    w.iConvexComb f i = w.iConvexComb (fun j => f j i) := isAffineMap_eval.map_iConvexComb ..

@[simp]
/--
lemma `convexCombPair_apply` / 引理 `convexCombPair_apply`

English:
lemma convexCombPair_apply
  given: (a b : R) (ha hb hab) (f g : ι ->₀ X) (i : ι)
  proof: isAffineMap_eval.map_convexCombPair ..

中文:
引理 convexCombPair_apply
  条件: (a b : R) (ha hb hab) (f g : ι ->₀ X) (i : ι)
  证明: isAffineMap_eval.map_convexCombPair ..

Depends on / 依赖: isAffineMap_eval, isAffineMap_eval.map_convexCombPair, map_convexCombPair
-/
lemma convexCombPair_apply (a b : R) (ha hb hab) (f g : ι ->₀ X) (i : ι) :
    convexCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i) :=
  isAffineMap_eval.map_convexCombPair ..

end Finsupp
