/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Order.UpperLower.Basic

/-!
# Definition of direct systems, inverse systems, and cardinalities in specific inverse systems

The first part of this file concerns directed systems: `DirectLimit` is defined as the quotient
of the disjoint union (`Sigma` type) by an equivalence relation (`Setoid`): compare
`CategoryTheory.Limits.Types.Quot`, which is a quotient by a plain relation.
Recursion and induction principles for constructing functions from and to `DirectLimit` and
proving things about elements in `DirectLimit`.

In the second part we compute the cardinality of each node in an inverse system `F i` indexed by a
well-order in which every map between successive nodes has constant fiber `X i`, and every limit
node is the `limit` of the inverse subsystem formed by all previous nodes.
(To avoid importing `Cardinal`, we in fact construct a bijection rather than
stating the result in terms of `Cardinal.mk`.)

The most tricky part of the whole argument happens at limit nodes: if `i : ι` is a limit,
what we have in hand is a family of bijections `F j ≃ ∀ l : Iio j, X l` for every `j < i`,
which we would like to "glue" up to a bijection `F i ≃ ∀ l : Iio i, X l`. We denote
`∀ l : Iio i, X l` by `PiLT X i`, and they form an inverse system just like the `F i`.
Observe that at a limit node `i`, `PiLT X i` is actually the inverse limit of `PiLT X j` over
all `j < i` (`piLTLim`). If the family of bijections `F j ≃ PiLT X j` is natural (`IsNatEquiv`),
we immediately obtain a bijection between the limits `limit F i ≃ PiLT X i` (`invLimEquiv`),
and we just need an additional bijection `F i ≃ limit F i` to obtain the desired
extension `F i ≃ PiLT X i` to the limit node `i`. (We do have such a bijection, for example, when
we consider a directed system of algebraic structures (say fields) `K i`, and `F` is
the inverse system of homomorphisms `K i ⟶ K` into a specific field `K`.)

Now our task reduces to the recursive construction of a *natural* family of bijections for each `i`.
We can prove that a natural family over all `l ≤ i` (`Iic i`) extends to a natural family over
`Iic i⁺` (where `i⁺ = succ i`), but at a limit node, recursion stops working: we have natural
families over all `Iic j` for each `j < i`, but we need to know that they glue together to form a
natural family over all `l < i` (`Iio i`). This intricacy did not occur to the author when he
thought he had a proof and set out to formalize it. Fortunately he was able to figure out an
additional `compat` condition (compatibility with the bijections `F i⁺ ≃ F i × X i` in the `X`
component) that guarantees uniqueness (`unique_pEquivOn`) and hence gluability (well-definedness):
see `pEquivOnGlue`. Instead of just a family of natural families, we actually construct a family of
the stronger `PEquivOn`s that bundles the `compat` condition, in order for the inductive argument
to work.

It is possible to circumvent the introduction of the `compat` condition using Zorn's lemma;
if there is a chain of natural families (i.e. for any two families in the chain, one is an
extension of the other) over lower sets (which are all of the form `Iic`, `Iio`, or `univ`),
we can clearly take the union to get a natural family that extends them all. If a maximal
natural family has domain `Iic i` or `Iio i` (`i` a limit), we already know how to extend it
one step further to `Iic i⁺` or `Iic i` respectively, so it must be the case that the domain
is everything. However, the author chose the `compat` approach in the end because it constructs
the distinguished bijection that is compatible with the projections to all `X i`.

-/

@[expose] public section

open Order Set

variable {ι : Type*} [Preorder ι] {F₁ F₂ F X : ι -> Type*}

variable (F) in
/--
Definition of `DirectedSystem` / `DirectedSystem` 的定义

English:
class DirectedSystem
  parameters: (f : forall ⦃i j⦄, i <= j -> F i -> F j)
  axioms and operations (2):
    - map_self(⦃i⦄ (x : F i)) : f le_rfl x = x
    - map_map(⦃k j i⦄ (hij : i <= j) (hjk : j <= k) (x : F i)) : f hjk (f hij x) = f (hij.trans hjk) x

中文:
类 DirectedSystem
  参数: (f : 对任意 ⦃i j⦄, i <= j -> F i -> F j)
  公理与运算 (2 个):
    - map_self(⦃i⦄ (x : F i)) : f le_rfl x = x
    - map_map(⦃k j i⦄ (hij : i <= j) (hjk : j <= k) (x : F i)) : f hjk (f hij x) = f (hij.trans hjk) x
-/
class DirectedSystem (f : forall ⦃i j⦄, i <= j -> F i -> F j) : Prop where
  map_self ⦃i⦄ (x : F i) : f le_rfl x = x
  map_map ⦃k j i⦄ (hij : i <= j) (hjk : j <= k) (x : F i) : f hjk (f hij x) = f (hij.trans hjk) x

section DirectedSystem

variable {T₁ : forall ⦃i j : ι⦄, i <= j -> Sort*} (f₁ : forall i j (h : i <= j), T₁ h)
variable [forall ⦃i j⦄ (h : i <= j), FunLike (T₁ h) (F₁ i) (F₁ j)] [DirectedSystem F₁ (f₁ · · ·)]
variable {T₂ : forall ⦃i j : ι⦄, i <= j -> Sort*} (f₂ : forall i j (h : i <= j), T₂ h)
variable [forall ⦃i j⦄ (h : i <= j), FunLike (T₂ h) (F₂ i) (F₂ j)] [DirectedSystem F₂ (f₂ · · ·)]
variable {T : forall ⦃i j : ι⦄, i <= j -> Sort*} (f : forall i j (h : i <= j), T h)
variable [forall ⦃i j⦄ (h : i <= j), FunLike (T h) (F i) (F j)] [DirectedSystem F (f · · ·)]

/--
theorem `DirectedSystem.map_self'` / 定理 `DirectedSystem.map_self'`

English:
theorem DirectedSystem.map_self'
  given: ⦃i⦄ (x)
  statement: f i i le_rfl x = x
  proof: DirectedSystem.map_self (f := (f · · ·)) x

中文:
定理 DirectedSystem.map_self'
  条件: ⦃i⦄ (x)
  结论: f i i le_rfl x = x
  证明: DirectedSystem.map_self (f := (f · · ·)) x

Depends on / 依赖: DirectedSystem, DirectedSystem.map_self, map_self
-/
theorem DirectedSystem.map_self' ⦃i⦄ (x) : f i i le_rfl x = x :=
  DirectedSystem.map_self (f := (f · · ·)) x

/--
theorem `DirectedSystem.map_map'` / 定理 `DirectedSystem.map_map'`

English:
theorem DirectedSystem.map_map'
  given: ⦃i j k⦄ (hij hjk x)
  proof: DirectedSystem.map_map (f := (f · · ·)) hij hjk x

中文:
定理 DirectedSystem.map_map'
  条件: ⦃i j k⦄ (hij hjk x)
  证明: DirectedSystem.map_map (f := (f · · ·)) hij hjk x

Depends on / 依赖: DirectedSystem, DirectedSystem.map_map, map_map
-/
theorem DirectedSystem.map_map' ⦃i j k⦄ (hij hjk x) :
    f j k hjk (f i j hij x) = f i k (hij.trans hjk) x :=
  DirectedSystem.map_map (f := (f · · ·)) hij hjk x

namespace DirectLimit
open DirectedSystem

variable [IsDirectedOrder ι]

/-- The setoid on the sigma type defining the direct limit. -/
@[instance_reducible]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: : Setoid (Σ i, F i) where
  body: existsᵉ (i) (hx : x.1 <= i) (hy : y.1 <= i), f _ _ hx x.2 = f _ _ hy y.2
  iseqv := ⟨fun x => ⟨x.1, le_rfl, le_rfl, rfl⟩, fun ⟨i, hx, hy, eq⟩ => ⟨i, hy, hx, eq.symm⟩,
    fun ⟨j, hx, _, jeq⟩ ⟨k, _, hz, keq⟩ =>
      have ⟨i, hji, hki⟩ := exists_ge_ge j k
      ⟨i, hx.trans hji, hz.trans hki, by
        rw [← map_map' _ hx hji]; rw [← map_map' _ hz hki]; rw [jeq]; rw [← keq]; rw [map_map']; rw [map_map']⟩⟩

中文:
定义 setoid
  签名: : 集合等价关系 (Σ i, F i) where
  定义体: existsᵉ (i) (hx : x.1 <= i) (hy : y.1 <= i), f _ _ hx x.2 = f _ _ hy y.2
  iseqv := ⟨fun x => ⟨x.1, le_rfl, le_rfl, rfl⟩, fun ⟨i, hx, hy, eq⟩ => ⟨i, hy, hx, eq.symm⟩,
    fun ⟨j, hx, _, jeq⟩ ⟨k, _, hz, keq⟩ =>
      have ⟨i, hji, hki⟩ := exists_ge_ge j k
      ⟨i, hx.trans hji, hz.trans hki, by
        rw [← map_map' _ hx hji]; rw [← map_map' _ hz hki]; rw [jeq]; rw [← keq]; rw [map_map']; rw [map_map']⟩⟩
-/
def setoid : Setoid (Σ i, F i) where
  r x y := existsᵉ (i) (hx : x.1 <= i) (hy : y.1 <= i), f _ _ hx x.2 = f _ _ hy y.2
  iseqv := ⟨fun x => ⟨x.1, le_rfl, le_rfl, rfl⟩, fun ⟨i, hx, hy, eq⟩ => ⟨i, hy, hx, eq.symm⟩,
    fun ⟨j, hx, _, jeq⟩ ⟨k, _, hz, keq⟩ =>
      have ⟨i, hji, hki⟩ := exists_ge_ge j k
      ⟨i, hx.trans hji, hz.trans hki, by
        rw [← map_map' _ hx hji]; rw [← map_map' _ hz hki]; rw [jeq]; rw [← keq]; rw [map_map']; rw [map_map']⟩⟩

/--
theorem `r_of_le` / 定理 `r_of_le`

English:
theorem r_of_le
  given: (x : Σ i, F i) (i : ι) (h : x.1 <= i)
  statement: (setoid f).r x ⟨i, f _ _ h x.2⟩
  proof: ⟨i, h, le_rfl, (map_map' _ _ _ _).symm⟩

中文:
定理 r_of_le
  条件: (x : Σ i, F i) (i : ι) (h : x.1 <= i)
  结论: (setoid f).r x ⟨i, f _ _ h x.2⟩
  证明: ⟨i, h, le_rfl, (map_map' _ _ _ _).symm⟩

Depends on / 依赖: le_rfl, map_map
-/
theorem r_of_le (x : Σ i, F i) (i : ι) (h : x.1 <= i) : (setoid f).r x ⟨i, f _ _ h x.2⟩ :=
  ⟨i, h, le_rfl, (map_map' _ _ _ _).symm⟩

variable (F) in
/--
Definition of `_root_.DirectLimit` / `_root_.DirectLimit` 的定义

English:
abbreviation _root_.DirectLimit
  signature: : Type _
  body: Quotient (setoid f)

中文:
缩写 _root_.DirectLimit
  签名: : 类型 _
  定义体: Quotient (setoid f)

Depends on / 依赖: Quotient, setoid
-/
abbrev _root_.DirectLimit : Type _ := Quotient (setoid f)

variable {f} in
/--
theorem `eq_of_le` / 定理 `eq_of_le`

English:
theorem eq_of_le
  given: (x : Σ i, F i) (i : ι) (h : x.1 <= i)
  proof: Quotient.sound (r_of_le _ x i h)

中文:
定理 eq_of_le
  条件: (x : Σ i, F i) (i : ι) (h : x.1 <= i)
  证明: Quotient.sound (r_of_le _ x i h)

Depends on / 依赖: Quotient, Quotient.sound, r_of_le
-/
theorem eq_of_le (x : Σ i, F i) (i : ι) (h : x.1 <= i) :
    (⟦x⟧ : DirectLimit F f) = ⟦⟨i, f _ _ h x.2⟩⟧ :=
  Quotient.sound (r_of_le _ x i h)

variable {f} in
@[simp]
/--
theorem `mk_apply` / 定理 `mk_apply`

English:
theorem mk_apply
  given: (i j : ι) (x : F i) (h : i <= j)
  proof: .symm eq_of_le ⟨_, x⟩ j h

中文:
定理 mk_apply
  条件: (i j : ι) (x : F i) (h : i <= j)
  证明: .symm eq_of_le ⟨_, x⟩ j h

Depends on / 依赖: eq_of_le
-/
theorem mk_apply (i j : ι) (x : F i) (h : i <= j) :
    ⟦⟨j, f _ _ h x⟩⟧ = (⟦⟨i, x⟩⟧ : DirectLimit F f) :=
.symm eq_of_le ⟨_, x⟩ j h

/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {C : DirectLimit F f -> Prop}
  proof: Quotient.ind (fun _ => ih _ _) x

中文:
定理 induction
  结论: {C : DirectLimit F f -> 命题}
  证明: Quotient.ind (fun _ => ih _ _) x
-/
@[elab_as_elim] protected theorem induction {C : DirectLimit F f -> Prop}
    (ih : forall i x, C ⟦⟨i, x⟩⟧) (x : DirectLimit F f) : C x :=
  Quotient.ind (fun _ => ih _ _) x

/--
theorem `exists_eq_mk` / 定理 `exists_eq_mk`

English:
theorem exists_eq_mk
  given: (z : DirectLimit F f)
  statement: exists i x, z = ⟦⟨i, x⟩⟧
  proof: by rcases z; exact ⟨_, _, rfl⟩

中文:
定理 存在_eq_mk
  条件: (z : DirectLimit F f)
  结论: 存在 i x, z = ⟦⟨i, x⟩⟧
  证明: by rcases z; exact ⟨_, _, rfl⟩
-/
theorem exists_eq_mk (z : DirectLimit F f) : exists i x, z = ⟦⟨i, x⟩⟧ := by rcases z; exact ⟨_, _, rfl⟩

/--
theorem `exists_eq_mk₂` / 定理 `exists_eq_mk₂`

English:
theorem exists_eq_mk₂
  given: (z w : DirectLimit F f)
  statement: exists i x y, z = ⟦⟨i, x⟩⟧ ∧ w = ⟦⟨i, y⟩⟧
  proof: z.inductionOn₂ w fun x y =>
    have ⟨i, hxi, hyi⟩ := exists_ge_ge x.1 y.1
    ⟨i, _, _, eq_of_le x i hxi, eq_of_le y i hyi⟩

中文:
定理 存在_eq_mk₂
  条件: (z w : DirectLimit F f)
  结论: 存在 i x y, z = ⟦⟨i, x⟩⟧ ∧ w = ⟦⟨i, y⟩⟧
  证明: z.inductionOn₂ w fun x y =>
    have ⟨i, hxi, hyi⟩ := exists_ge_ge x.1 y.1
    ⟨i, _, _, eq_of_le x i hxi, eq_of_le y i hyi⟩

Depends on / 依赖: eq_of_le, exists_ge_ge, z.inductionOn
-/
theorem exists_eq_mk₂ (z w : DirectLimit F f) : exists i x y, z = ⟦⟨i, x⟩⟧ ∧ w = ⟦⟨i, y⟩⟧ :=
  z.inductionOn₂ w fun x y =>
    have ⟨i, hxi, hyi⟩ := exists_ge_ge x.1 y.1
    ⟨i, _, _, eq_of_le x i hxi, eq_of_le y i hyi⟩

/--
theorem `exists_eq_mk₃` / 定理 `exists_eq_mk₃`

English:
theorem exists_eq_mk₃
  given: (w u v : DirectLimit F f)
  proof: w.inductionOn₃ u v fun x y z =>
    have ⟨i, hxi, hyi, hzi⟩ := directed_of₃ (· <= ·) x.1 y.1 z.1
    ⟨i, _, _, _, eq_of_le x i hxi, eq_of_le y i hyi, eq_of_le z i hzi⟩

中文:
定理 存在_eq_mk₃
  条件: (w u v : DirectLimit F f)
  证明: w.inductionOn₃ u v fun x y z =>
    have ⟨i, hxi, hyi, hzi⟩ := directed_of₃ (· <= ·) x.1 y.1 z.1
    ⟨i, _, _, _, eq_of_le x i hxi, eq_of_le y i hyi, eq_of_le z i hzi⟩

Depends on / 依赖: eq_of_le, w.inductionOn
-/
theorem exists_eq_mk₃ (w u v : DirectLimit F f) :
    exists i x y z, w = ⟦⟨i, x⟩⟧ ∧ u = ⟦⟨i, y⟩⟧ ∧ v = ⟦⟨i, z⟩⟧ :=
  w.inductionOn₃ u v fun x y z =>
    have ⟨i, hxi, hyi, hzi⟩ := directed_of₃ (· <= ·) x.1 y.1 z.1
    ⟨i, _, _, _, eq_of_le x i hxi, eq_of_le y i hyi, eq_of_le z i hzi⟩

/--
theorem `induction₂` / 定理 `induction₂`

English:
theorem induction₂
  statement: {C : DirectLimit F f -> DirectLimit F f -> Prop}
  proof: by
  obtain ⟨_, _, _, rfl, rfl⟩ := exists_eq_mk₂ f x y; apply ih

中文:
定理 induction₂
  结论: {C : DirectLimit F f -> DirectLimit F f -> 命题}
  证明: by
  obtain ⟨_, _, _, rfl, rfl⟩ := exists_eq_mk₂ f x y; apply ih
-/
@[elab_as_elim] protected theorem induction₂ {C : DirectLimit F f -> DirectLimit F f -> Prop}
    (ih : forall i x y, C ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧) (x y : DirectLimit F f) : C x y := by
  obtain ⟨_, _, _, rfl, rfl⟩ := exists_eq_mk₂ f x y; apply ih

/--
theorem `induction₃` / 定理 `induction₃`

English:
theorem induction₃
  proof: by
  obtain ⟨_, _, _, _, rfl, rfl, rfl⟩ := exists_eq_mk₃ f x y z; apply ih

中文:
定理 induction₃
  证明: by
  obtain ⟨_, _, _, _, rfl, rfl, rfl⟩ := exists_eq_mk₃ f x y z; apply ih
-/
@[elab_as_elim] protected theorem induction₃
    {C : DirectLimit F f -> DirectLimit F f -> DirectLimit F f -> Prop}
    (ih : forall i x y z, C ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ ⟦⟨i, z⟩⟧) (x y z : DirectLimit F f) : C x y z := by
  obtain ⟨_, _, _, _, rfl, rfl, rfl⟩ := exists_eq_mk₃ f x y z; apply ih

/--
theorem `mk_injective` / 定理 `mk_injective`

English:
theorem mk_injective
  given: (h : forall i j hij, Function.Injective (f i j hij)) (i)
  proof: fun _ _ eq => have ⟨_, _, _, eq⟩ := Quotient.eq.mp eq; h _ _ _ eq

中文:
定理 mk_injective
  条件: (h : 对任意 i j hij, 函数.单射 (f i j hij)) (i)
  证明: fun _ _ eq => have ⟨_, _, _, eq⟩ := Quotient.eq.mp eq; h _ _ _ eq

Depends on / 依赖: Quotient, Quotient.eq.mp
-/
theorem mk_injective (h : forall i j hij, Function.Injective (f i j hij)) (i) :
    Function.Injective fun x => (⟦⟨i, x⟩⟧ : DirectLimit F f) :=
  fun _ _ eq => have ⟨_, _, _, eq⟩ := Quotient.eq.mp eq; h _ _ _ eq

section map₀

variable [Nonempty ι] (ih : forall i, F i)

/--
Definition of `map₀` / `map₀` 的定义

English:
definition map₀
  signature: : DirectLimit F f
  body: ⟦⟨Classical.arbitrary ι, ih _⟩⟧

中文:
定义 map₀
  签名: : DirectLimit F f
  定义体: ⟦⟨Classical.arbitrary ι, ih _⟩⟧

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
noncomputable def map₀ : DirectLimit F f := ⟦⟨Classical.arbitrary ι, ih _⟩⟧

/--
theorem `map₀_def` / 定理 `map₀_def`

English:
theorem map₀_def
  given: (compat : forall i j h, f i j h (ih i) = ih j) (i)
  statement: map₀ f ih = ⟦⟨i, ih i⟩⟧
  proof: have ⟨j, hcj, hij⟩ := exists_ge_ge (Classical.arbitrary ι) i
  Quotient.sound ⟨j, hcj, hij, (compat ..).trans (compat ..).symm⟩

中文:
定理 map₀_def
  条件: (compat : 对任意 i j h, f i j h (ih i) = ih j) (i)
  结论: map₀ f ih = ⟦⟨i, ih i⟩⟧
  证明: have ⟨j, hcj, hij⟩ := exists_ge_ge (Classical.arbitrary ι) i
  Quotient.sound ⟨j, hcj, hij, (compat ..).trans (compat ..).symm⟩

Depends on / 依赖: Classical, Classical.arbitrary, Quotient, Quotient.sound, arbitrary, compat, exists_ge_ge
-/
theorem map₀_def (compat : forall i j h, f i j h (ih i) = ih j) (i) : map₀ f ih = ⟦⟨i, ih i⟩⟧ :=
  have ⟨j, hcj, hij⟩ := exists_ge_ge (Classical.arbitrary ι) i
  Quotient.sound ⟨j, hcj, hij, (compat ..).trans (compat ..).symm⟩

end map₀

section lift

variable {C : Sort*} (ih : forall i, F i -> C) (compat : forall i j h x, ih i x = ih j (f i j h x))

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (z : DirectLimit F f)
  body: z.recOn (fun x => ih x.1 x.2) fun x y ⟨k, hxk, hyk, eq⟩ => by
    simp_rw [eq_rec_constant, compat _ _ hxk, compat _ _ hyk, eq]

@[simp]

中文:
定义 lift
  签名: (z : DirectLimit F f)
  定义体: z.recOn (fun x => ih x.1 x.2) fun x y ⟨k, hxk, hyk, eq⟩ => by
    simp_rw [eq_rec_constant, compat _ _ hxk, compat _ _ hyk, eq]

@[simp]
-/
protected def lift (z : DirectLimit F f) : C :=
  z.recOn (fun x => ih x.1 x.2) fun x y ⟨k, hxk, hyk, eq⟩ => by
    simp_rw [eq_rec_constant, compat _ _ hxk, compat _ _ hyk, eq]

@[simp]
/--
theorem `lift_def` / 定理 `lift_def`

English:
theorem lift_def
  given: (x)
  statement: DirectLimit.lift f ih compat ⟦x⟧ = ih x.1 x.2
  proof: rfl

中文:
定理 lift_def
  条件: (x)
  结论: DirectLimit.lift f ih compat ⟦x⟧ = ih x.1 x.2
  证明: rfl
-/
theorem lift_def (x) : DirectLimit.lift f ih compat ⟦x⟧ = ih x.1 x.2 := rfl

/--
theorem `lift_injective` / 定理 `lift_injective`

English:
theorem lift_injective
  given: (h : forall i, Function.Injective (ih i))
  proof: DirectLimit.induction₂ _ fun i x y eq => by simp_rw [lift_def] at eq; rw [h i eq]

中文:
定理 lift_injective
  条件: (h : 对任意 i, 函数.单射 (ih i))
  证明: DirectLimit.induction₂ _ fun i x y eq => by simp_rw [lift_def] at eq; rw [h i eq]

Depends on / 依赖: DirectLimit, DirectLimit.induction, lift_def, simp_rw
-/
theorem lift_injective (h : forall i, Function.Injective (ih i)) :
    Function.Injective (DirectLimit.lift f ih compat) :=
  DirectLimit.induction₂ _ fun i x y eq => by simp_rw [lift_def] at eq; rw [h i eq]

end lift

section map

variable (ih : forall i, F₁ i -> F₂ i) (compat : forall i j h x, f₂ i j h (ih i x) = ih j (f₁ i j h x))

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (z : DirectLimit F₁ f₁)
  body: z.lift _ (fun i x => ⟦⟨i, ih i x⟩⟧) fun j k h x => Quotient.sound
    have ⟨i, hji, hki⟩ := exists_ge_ge j k
    ⟨i, hji, hki, by simp_rw [compat, map_map']⟩

中文:
定义 map
  签名: (z : DirectLimit F₁ f₁)
  定义体: z.lift _ (fun i x => ⟦⟨i, ih i x⟩⟧) fun j k h x => Quotient.sound
    have ⟨i, hji, hki⟩ := exists_ge_ge j k
    ⟨i, hji, hki, by simp_rw [compat, map_map']⟩

Depends on / 依赖: Quotient, Quotient.sound, compat, exists_ge_ge, map_map, simp_rw, z.lift
-/
def map (z : DirectLimit F₁ f₁) : DirectLimit F₂ f₂ :=
z.lift _ (fun i x => ⟦⟨i, ih i x⟩⟧) fun j k h x => Quotient.sound
    have ⟨i, hji, hki⟩ := exists_ge_ge j k
    ⟨i, hji, hki, by simp_rw [compat, map_map']⟩

/--
theorem `map_def` / 定理 `map_def`

English:
theorem map_def
  given: (x)
  statement: map f₁ f₂ ih compat ⟦x⟧ = ⟦⟨x.1, ih x.1 x.2⟩⟧
  proof: rfl

中文:
定理 map_def
  条件: (x)
  结论: map f₁ f₂ ih compat ⟦x⟧ = ⟦⟨x.1, ih x.1 x.2⟩⟧
  证明: rfl
-/
theorem map_def (x) : map f₁ f₂ ih compat ⟦x⟧ = ⟦⟨x.1, ih x.1 x.2⟩⟧ := rfl

end map

section lift₂

variable {C : Sort*} (ih : forall i, F₁ i -> F₂ i -> C)
  (compat : forall i j h x y, ih i x y = ih j (f₁ i j h x) (f₂ i j h y))

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def lift₂Aux (z : Σ i, F₁ i) (w : Σ i, F₂ i)
  body: by
  choose j hzj hwj using exists_ge_ge z.1 w.1
  refine ⟨ih j (f₁ _ _ hzj z.2) (f₂ _ _ hwj w.2), fun k hzk hwk => ?_⟩
  have ⟨i, hji, hki⟩ := exists_ge_ge j k
  simp_rw [compat _ _ hji, compat _ _ hki, map_map']

中文:
定义 noncomputable
  签名: def lift₂Aux (z : Σ i, F₁ i) (w : Σ i, F₂ i)
  定义体: by
  choose j hzj hwj using exists_ge_ge z.1 w.1
  refine ⟨ih j (f₁ _ _ hzj z.2) (f₂ _ _ hwj w.2), fun k hzk hwk => ?_⟩
  have ⟨i, hji, hki⟩ := exists_ge_ge j k
  simp_rw [compat _ _ hji, compat _ _ hki, map_map']
-/
private noncomputable def lift₂Aux (z : Σ i, F₁ i) (w : Σ i, F₂ i) :
    {x : C // forall i (hzi : z.1 <= i) (hwi : w.1 <= i), x = ih i (f₁ _ _ hzi z.2) (f₂ _ _ hwi w.2)} := by
  choose j hzj hwj using exists_ge_ge z.1 w.1
  refine ⟨ih j (f₁ _ _ hzj z.2) (f₂ _ _ hwj w.2), fun k hzk hwk => ?_⟩
  have ⟨i, hji, hki⟩ := exists_ge_ge j k
  simp_rw [compat _ _ hji, compat _ _ hki, map_map']

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def lift₂ (z : DirectLimit F₁ f₁) (w : DirectLimit F₂ f₂)
  body: z.hrecOn₂ w (φ := fun _ _ => C) (lift₂Aux f₁ f₂ ih compat · ·)
fun _ _ _ _ ⟨j, hx, hyj, jeq⟩ ⟨k, hyk, hz, keq⟩ => heq_of_eq by
      have ⟨i, hji, hki⟩ := exists_ge_ge j k
      simp_rw [(lift₂Aux ..).2 _ (hx.trans hji) (hyk.trans hki),
        (lift₂Aux ..).2 _ (hyj.trans hji) (hz.trans hki),
        ← map_map' _ hx hji, jeq, ← map_map' _ hz hki, ← keq, map_map']

中文:
定义 noncomputable
  签名: def lift₂ (z : DirectLimit F₁ f₁) (w : DirectLimit F₂ f₂)
  定义体: z.hrecOn₂ w (φ := fun _ _ => C) (lift₂Aux f₁ f₂ ih compat · ·)
fun _ _ _ _ ⟨j, hx, hyj, jeq⟩ ⟨k, hyk, hz, keq⟩ => heq_of_eq by
      have ⟨i, hji, hki⟩ := exists_ge_ge j k
      simp_rw [(lift₂Aux ..).2 _ (hx.trans hji) (hyk.trans hki),
        (lift₂Aux ..).2 _ (hyj.trans hji) (hz.trans hki),
        ← map_map' _ hx hji, jeq, ← map_map' _ hz hki, ← keq, map_map']
-/
protected noncomputable def lift₂ (z : DirectLimit F₁ f₁) (w : DirectLimit F₂ f₂) : C :=
  z.hrecOn₂ w (φ := fun _ _ => C) (lift₂Aux f₁ f₂ ih compat · ·)
fun _ _ _ _ ⟨j, hx, hyj, jeq⟩ ⟨k, hyk, hz, keq⟩ => heq_of_eq by
      have ⟨i, hji, hki⟩ := exists_ge_ge j k
      simp_rw [(lift₂Aux ..).2 _ (hx.trans hji) (hyk.trans hki),
        (lift₂Aux ..).2 _ (hyj.trans hji) (hz.trans hki),
        ← map_map' _ hx hji, jeq, ← map_map' _ hz hki, ← keq, map_map']

/--
theorem `lift₂_def₂` / 定理 `lift₂_def₂`

English:
theorem lift₂_def₂
  given: (x : Σ i, F₁ i) (y : Σ i, F₂ i) (i) (hxi : x.1 <= i) (hyi : y.1 <= i)
  proof: (lift₂Aux _ _ _ compat _ _).2 ..

中文:
定理 lift₂_def₂
  条件: (x : Σ i, F₁ i) (y : Σ i, F₂ i) (i) (hxi : x.1 <= i) (hyi : y.1 <= i)
  证明: (lift₂Aux _ _ _ compat _ _).2 ..

Depends on / 依赖: compat
-/
theorem lift₂_def₂ (x : Σ i, F₁ i) (y : Σ i, F₂ i) (i) (hxi : x.1 <= i) (hyi : y.1 <= i) :
    DirectLimit.lift₂ f₁ f₂ ih compat ⟦x⟧ ⟦y⟧ = ih i (f₁ _ _ hxi x.2) (f₂ _ _ hyi y.2) :=
  (lift₂Aux _ _ _ compat _ _).2 ..

/--
theorem `lift₂_def` / 定理 `lift₂_def`

English:
theorem lift₂_def
  given: (i x y)
  statement: DirectLimit.lift₂ f₁ f₂ ih compat ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = ih i x y
  proof: by
  rw [lift₂_def₂ _ _ _ _ _ _ i le_rfl le_rfl]; rw [map_self']; rw [map_self']

中文:
定理 lift₂_def
  条件: (i x y)
  结论: DirectLimit.lift₂ f₁ f₂ ih compat ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = ih i x y
  证明: by
  rw [lift₂_def₂ _ _ _ _ _ _ i le_rfl le_rfl]; rw [map_self']; rw [map_self']

Depends on / 依赖: le_rfl, map_self
-/
theorem lift₂_def (i x y) : DirectLimit.lift₂ f₁ f₂ ih compat ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = ih i x y := by
  rw [lift₂_def₂ _ _ _ _ _ _ i le_rfl le_rfl]; rw [map_self']; rw [map_self']

end lift₂

section map₂

variable (ih : forall i, F₁ i -> F₂ i -> F i)
  (compat : forall i j h x y, f i j h (ih i x y) = ih j (f₁ i j h x) (f₂ i j h y))

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: : DirectLimit F₁ f₁ -> DirectLimit F₂ f₂ -> DirectLimit F f
  body: DirectLimit.lift₂ f₁ f₂ (fun i x y => ⟦⟨i, ih i x y⟩⟧) fun j k h x y => Quotient.sound
    have ⟨i, hji, hki⟩ := exists_ge_ge j k
    ⟨i, hji, hki, by simp_rw [compat, map_map']⟩

中文:
定义 map₂
  签名: : DirectLimit F₁ f₁ -> DirectLimit F₂ f₂ -> DirectLimit F f
  定义体: DirectLimit.lift₂ f₁ f₂ (fun i x y => ⟦⟨i, ih i x y⟩⟧) fun j k h x y => Quotient.sound
    have ⟨i, hji, hki⟩ := exists_ge_ge j k
    ⟨i, hji, hki, by simp_rw [compat, map_map']⟩

Depends on / 依赖: DirectLimit, DirectLimit.lift, Quotient, Quotient.sound, compat, exists_ge_ge, map_map, simp_rw
-/
noncomputable def map₂ : DirectLimit F₁ f₁ -> DirectLimit F₂ f₂ -> DirectLimit F f :=
DirectLimit.lift₂ f₁ f₂ (fun i x y => ⟦⟨i, ih i x y⟩⟧) fun j k h x y => Quotient.sound
    have ⟨i, hji, hki⟩ := exists_ge_ge j k
    ⟨i, hji, hki, by simp_rw [compat, map_map']⟩

/--
theorem `map₂_def₂` / 定理 `map₂_def₂`

English:
theorem map₂_def₂
  given: (x y) (i) (hxi : x.1 <= i) (hyi : y.1 <= i)
  proof: lift₂_def₂ ..

中文:
定理 map₂_def₂
  条件: (x y) (i) (hxi : x.1 <= i) (hyi : y.1 <= i)
  证明: lift₂_def₂ ..
-/
theorem map₂_def₂ (x y) (i) (hxi : x.1 <= i) (hyi : y.1 <= i) :
    map₂ f₁ f₂ f ih compat ⟦x⟧ ⟦y⟧ = ⟦⟨i, ih i (f₁ _ _ hxi x.2) (f₂ _ _ hyi y.2)⟩⟧ :=
  lift₂_def₂ ..

/--
theorem `map₂_def` / 定理 `map₂_def`

English:
theorem map₂_def
  given: (i x y)
  statement: map₂ f₁ f₂ f ih compat ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = ⟦⟨i, ih i x y⟩⟧
  proof: lift₂_def ..

中文:
定理 map₂_def
  条件: (i x y)
  结论: map₂ f₁ f₂ f ih compat ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = ⟦⟨i, ih i x y⟩⟧
  证明: lift₂_def ..
-/
theorem map₂_def (i x y) : map₂ f₁ f₂ f ih compat ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = ⟦⟨i, ih i x y⟩⟧ :=
  lift₂_def ..

end map₂

end DirectLimit

end DirectedSystem

variable (f : forall ⦃i j : ι⦄, i <= j -> F j -> F i) ⦃i j : ι⦄ (h : i <= j)

/--
Definition of `InverseSystem` / `InverseSystem` 的定义

English:
class InverseSystem
  parameters: : Prop where
  axioms and operations (2):
    - map_self(⦃i) : ι⦄ (x : F i) : f le_rfl x = x
    - map_map(⦃k j i) : ι⦄ (hkj : k <= j) (hji : j <= i) (x : F i) : f hkj (f hji x) = f (hkj.trans hji) x

中文:
类 InverseSystem
  参数: : 命题 where
  公理与运算 (2 个):
    - map_self(⦃i) : ι⦄ (x : F i) : f le_rfl x = x
    - map_map(⦃k j i) : ι⦄ (hkj : k <= j) (hji : j <= i) (x : F i) : f hkj (f hji x) = f (hkj.trans hji) x
-/
class InverseSystem : Prop where
  map_self ⦃i : ι⦄ (x : F i) : f le_rfl x = x
  map_map ⦃k j i : ι⦄ (hkj : k <= j) (hji : j <= i) (x : F i) : f hkj (f hji x) = f (hkj.trans hji) x

namespace InverseSystem

section proj

/--
Definition of `limit` / `limit` 的定义

English:
definition limit
  signature: (i : ι)
  body: {F | forall ⦃j k⦄ (h : j.1 <= k.1), f h (F k) = F j}

中文:
定义 limit
  签名: (i : ι)
  定义体: {F | forall ⦃j k⦄ (h : j.1 <= k.1), f h (F k) = F j}
-/
def limit (i : ι) : Set (forall l : Iio i, F l) :=
  {F | forall ⦃j k⦄ (h : j.1 <= k.1), f h (F k) = F j}

/--
Definition of `piLT` / `piLT` 的定义

English:
abbreviation piLT
  signature: (X : ι -> Type*) (i : ι)
  body: forall l : Iio i, X l

中文:
缩写 piLT
  签名: (X : ι -> 类型) (i : ι)
  定义体: forall l : Iio i, X l
-/
abbrev piLT (X : ι -> Type*) (i : ι) := forall l : Iio i, X l

/--
Definition of `piLTProj` / `piLTProj` 的定义

English:
abbreviation piLTProj
  signature: (f : piLT X j)
  body: fun l => f ⟨l, l.2.trans_le h⟩

中文:
缩写 piLTProj
  签名: (f : piLT X j)
  定义体: fun l => f ⟨l, l.2.trans_le h⟩

Depends on / 依赖: trans_le
-/
abbrev piLTProj (f : piLT X j) : piLT X i := fun l => f ⟨l, l.2.trans_le h⟩

/--
theorem `piLTProj_intro` / 定理 `piLTProj_intro`

English:
theorem piLTProj_intro
  given: {l : Iio j} {f : piLT X j} (hl : l < i)
  proof: rfl

中文:
定理 piLTProj_intro
  条件: {l : 左无界右开区间 j} {f : piLT X j} (hl : l < i)
  证明: rfl
-/
theorem piLTProj_intro {l : Iio j} {f : piLT X j} (hl : l < i) :
    f l = piLTProj h f ⟨l, hl⟩ := rfl

/--
Definition of `IsNatEquiv` / `IsNatEquiv` 的定义

English:
definition IsNatEquiv
  signature: {s : Set ι} (equiv : forall j : s, F j ≃ piLT X j)
  body: forall ⦃j k⦄ (hj : j in s) (hk : k in s) (h : k <= j) (x : F j),
    equiv ⟨k, hk⟩ (f h x) = piLTProj h (equiv ⟨j, hj⟩ x)

中文:
定义 Is自然数Equiv
  签名: {s : 集合 ι} (equiv : 对任意 j : s, F j ≃ piLT X j)
  定义体: forall ⦃j k⦄ (hj : j in s) (hk : k in s) (h : k <= j) (x : F j),
    equiv ⟨k, hk⟩ (f h x) = piLTProj h (equiv ⟨j, hj⟩ x)

Depends on / 依赖: piLTProj
-/
def IsNatEquiv {s : Set ι} (equiv : forall j : s, F j ≃ piLT X j) : Prop :=
  forall ⦃j k⦄ (hj : j in s) (hk : k in s) (h : k <= j) (x : F j),
    equiv ⟨k, hk⟩ (f h x) = piLTProj h (equiv ⟨j, hj⟩ x)

variable {ι : Type*} [LinearOrder ι] {X : ι -> Type*} {i : ι} (hi : IsSuccPrelimit i)

/--
Definition of `piLTLim` / `piLTLim` 的定义

English:
definition piLTLim
  signature: : piLT X i ≃ limit (piLTProj (X := X)) i where
  body: ⟨fun j => piLTProj j.2.le f, fun _ _ _ => rfl⟩
  invFun f l := let k := hi.mid l.2; f.1 ⟨k, k.2.2⟩ ⟨l, k.2.1⟩
  right_inv f := by
    ext j l
    set k := hi.mid (l.2.trans j.2)
    obtain le | le := le_total j ⟨k, k.2.2⟩
    exacts [congr_fun (f.2 le) l, (congr_fun (f.2 le) ⟨l, _⟩).symm]

中文:
定义 piLTLim
  签名: : piLT X i ≃ limit (piLTProj (X := X)) i where
  定义体: ⟨fun j => piLTProj j.2.le f, fun _ _ _ => rfl⟩
  invFun f l := let k := hi.mid l.2; f.1 ⟨k, k.2.2⟩ ⟨l, k.2.1⟩
  right_inv f := by
    ext j l
    set k := hi.mid (l.2.trans j.2)
    obtain le | le := le_total j ⟨k, k.2.2⟩
    exacts [congr_fun (f.2 le) l, (congr_fun (f.2 le) ⟨l, _⟩).symm]
-/
@[simps apply] noncomputable def piLTLim : piLT X i ≃ limit (piLTProj (X := X)) i where
  toFun f := ⟨fun j => piLTProj j.2.le f, fun _ _ _ => rfl⟩
  invFun f l := let k := hi.mid l.2; f.1 ⟨k, k.2.2⟩ ⟨l, k.2.1⟩
  right_inv f := by
    ext j l
    set k := hi.mid (l.2.trans j.2)
    obtain le | le := le_total j ⟨k, k.2.2⟩
    exacts [congr_fun (f.2 le) l, (congr_fun (f.2 le) ⟨l, _⟩).symm]

/--
theorem `piLTLim_symm_apply` / 定理 `piLTLim_symm_apply`

English:
theorem piLTLim_symm_apply
  given: {f} (k : Iio i) {l : Iio i} (hl : l.1 < k.1)
  proof: by
  conv_rhs => rw [← (piLTLim hi).right_inv f]
  rfl

中文:
定理 piLTLim_symm_apply
  条件: {f} (k : 左无界右开区间 i) {l : 左无界右开区间 i} (hl : l.1 < k.1)
  证明: by
  conv_rhs => rw [← (piLTLim hi).right_inv f]
  rfl

Depends on / 依赖: conv_rhs, piLTLim, right_inv
-/
theorem piLTLim_symm_apply {f} (k : Iio i) {l : Iio i} (hl : l.1 < k.1) :
    (piLTLim (X := X) hi).symm f l = f.1 k ⟨l, hl⟩ := by
  conv_rhs => rw [← (piLTLim hi).right_inv f]
  rfl

end proj

variable {ι : Type*} {F X : ι -> Type*} {i : ι}

section

variable [PartialOrder ι] [DecidableEq ι]

/--
Definition of `piSplitLE` / `piSplitLE` 的定义

English:
definition piSplitLE
  signature: : piLT X i × X i ≃ forall j : Iic i, X j where
  body: if h : j = i then h.symm ▸ f.2 else f.1 ⟨j, j.2.lt_of_ne h⟩
  invFun f := (fun j => f ⟨j, j.2.le⟩, f ⟨i, le_rfl⟩)
  left_inv f := by ext j; exacts [dif_neg j.2.ne, dif_pos rfl]
  right_inv f := by grind

中文:
定义 piSplitLE
  签名: : piLT X i × X i ≃ 对任意 j : 左无界右闭区间 i, X j where
  定义体: if h : j = i then h.symm ▸ f.2 else f.1 ⟨j, j.2.lt_of_ne h⟩
  invFun f := (fun j => f ⟨j, j.2.le⟩, f ⟨i, le_rfl⟩)
  left_inv f := by ext j; exacts [dif_neg j.2.ne, dif_pos rfl]
  right_inv f := by grind

Depends on / 依赖: h.symm, lt_of_ne
-/
def piSplitLE : piLT X i × X i ≃ forall j : Iic i, X j where
  toFun f j := if h : j = i then h.symm ▸ f.2 else f.1 ⟨j, j.2.lt_of_ne h⟩
  invFun f := (fun j => f ⟨j, j.2.le⟩, f ⟨i, le_rfl⟩)
  left_inv f := by ext j; exacts [dif_neg j.2.ne, dif_pos rfl]
  right_inv f := by grind

set_option backward.isDefEq.respectTransparency false in
/--
theorem `piSplitLE_eq` / 定理 `piSplitLE_eq`

English:
theorem piSplitLE_eq
  given: {f : piLT X i × X i}
  proof: by simp [piSplitLE]

中文:
定理 piSplitLE_eq
  条件: {f : piLT X i × X i}
  证明: by simp [piSplitLE]
-/
@[simp] theorem piSplitLE_eq {f : piLT X i × X i} :
    piSplitLE f ⟨i, le_rfl⟩ = f.2 := by simp [piSplitLE]

/--
theorem `piSplitLE_lt` / 定理 `piSplitLE_lt`

English:
theorem piSplitLE_lt
  given: {f : piLT X i × X i} {j} (hj : j < i)
  proof: dif_neg hj.ne

中文:
定理 piSplitLE_lt
  条件: {f : piLT X i × X i} {j} (hj : j < i)
  证明: dif_neg hj.ne

Depends on / 依赖: dif_neg, hj.ne
-/
theorem piSplitLE_lt {f : piLT X i × X i} {j} (hj : j < i) :
    piSplitLE f ⟨j, hj.le⟩ = f.1 ⟨j, hj⟩ := dif_neg hj.ne

end

variable [LinearOrder ι] {f : forall ⦃i j : ι⦄, i <= j -> F j -> F i}

local postfix:max "⁺" => succ -- Note: conflicts with `PosPart` notation

section Succ

variable [SuccOrder ι]
variable (equiv : forall j : Iic i, F j ≃ piLT X j) (e : F i⁺ ≃ F i × X i) (hi : ¬ IsMax i)

/--
Definition of `piEquivSucc` / `piEquivSucc` 的定义

English:
definition piEquivSucc
  signature: : forall j : Iic i⁺, F j ≃ piLT X j
  body: piSplitLE (X := fun i => F i ≃ piLT X i)
  (fun j => equiv ⟨j, (lt_succ_iff_of_not_isMax hi).mp j.2⟩,
e.trans ((equiv ⟨i, le_rfl⟩).prodCongr <| Equiv.refl _).trans piSplitLE.trans
Equiv.piCongrSet Set.ext fun _ => (lt_succ_iff_of_not_isMax hi).symm)

中文:
定义 piEquivSucc
  签名: : 对任意 j : 左无界右闭区间 i⁺, F j ≃ piLT X j
  定义体: piSplitLE (X := fun i => F i ≃ piLT X i)
  (fun j => equiv ⟨j, (lt_succ_iff_of_not_isMax hi).mp j.2⟩,
e.trans ((equiv ⟨i, le_rfl⟩).prodCongr <| Equiv.refl _).trans piSplitLE.trans
Equiv.piCongrSet Set.ext fun _ => (lt_succ_iff_of_not_isMax hi).symm)

Depends on / 依赖: Equiv.piCongrSet, Equiv.refl, Set.ext, e.trans, le_rfl, lt_succ_iff_of_not_isMax, piCongrSet, piSplitLE, piSplitLE.trans, prodCongr
-/
def piEquivSucc : forall j : Iic i⁺, F j ≃ piLT X j :=
  piSplitLE (X := fun i => F i ≃ piLT X i)
  (fun j => equiv ⟨j, (lt_succ_iff_of_not_isMax hi).mp j.2⟩,
e.trans ((equiv ⟨i, le_rfl⟩).prodCongr <| Equiv.refl _).trans piSplitLE.trans
Equiv.piCongrSet Set.ext fun _ => (lt_succ_iff_of_not_isMax hi).symm)

/--
theorem `piEquivSucc_self` / 定理 `piEquivSucc_self`

English:
theorem piEquivSucc_self
  given: {x}
  proof: by
  simp [piEquivSucc]

中文:
定理 piEquivSucc_self
  条件: {x}
  证明: by
  simp [piEquivSucc]

Depends on / 依赖: piEquivSucc
-/
theorem piEquivSucc_self {x} :
    piEquivSucc equiv e hi ⟨_, le_rfl⟩ x ⟨i, lt_succ_of_not_isMax hi⟩ = (e x).2 := by
  simp [piEquivSucc]

variable {equiv e}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isNatEquiv_piEquivSucc` / 定理 `isNatEquiv_piEquivSucc`

English:
theorem isNatEquiv_piEquivSucc
  statement: [InverseSystem f] (H : forall x, (e x).1 = f (le_succ i) x)
  proof: fun j k hj hk h x => by
  have lt_succ {j} := (lt_succ_iff_of_not_isMax (b := j) hi).mpr
  obtain rfl | hj := le_succ_iff_eq_or_le.mp hj
  · obtain rfl | hk := le_succ_iff_eq_or_le.mp hk
    · simp [InverseSystem.map_self]
    · funext l
      rw [piEquivSucc]; rw [piSplitLE_lt (lt_succ hk)]; rw [← InverseSystem.map_map (f := f) hk (le_succ i)]; rw [← H]; rw [piLTProj]; rw [nat le_rfl]
      simp [piSplitLE_lt (l.2.trans_le hk)]
  · rw [piEquivSucc, piSplitLE_lt (h.trans_lt <| lt_succ hj), nat hj, piSplitLE_lt (lt_succ hj)]

中文:
定理 is自然数Equiv_piEquivSucc
  结论: [InverseSystem f] (H : 对任意 x, (e x).1 = f (le_succ i) x)
  证明: fun j k hj hk h x => by
  have lt_succ {j} := (lt_succ_iff_of_not_isMax (b := j) hi).mpr
  obtain rfl | hj := le_succ_iff_eq_or_le.mp hj
  · obtain rfl | hk := le_succ_iff_eq_or_le.mp hk
    · simp [InverseSystem.map_self]
    · funext l
      rw [piEquivSucc]; rw [piSplitLE_lt (lt_succ hk)]; rw [← InverseSystem.map_map (f := f) hk (le_succ i)]; rw [← H]; rw [piLTProj]; rw [nat le_rfl]
      simp [piSplitLE_lt (l.2.trans_le hk)]
  · rw [piEquivSucc, piSplitLE_lt (h.trans_lt <| lt_succ hj), nat hj, piSplitLE_lt (lt_succ hj)]

Depends on / 依赖: InverseSystem, InverseSystem.map_map, InverseSystem.map_self, h.trans_lt, le_rfl, le_succ, le_succ_iff_eq_or_le, le_succ_iff_eq_or_le.mp, lt_succ, lt_succ_iff_of_not_isMax, map_map, map_self, piEquivSucc, piLTProj, piSplitLE_lt, trans_le, trans_lt
-/
theorem isNatEquiv_piEquivSucc [InverseSystem f] (H : forall x, (e x).1 = f (le_succ i) x)
    (nat : IsNatEquiv f equiv) : IsNatEquiv f (piEquivSucc equiv e hi) := fun j k hj hk h x => by
  have lt_succ {j} := (lt_succ_iff_of_not_isMax (b := j) hi).mpr
  obtain rfl | hj := le_succ_iff_eq_or_le.mp hj
  · obtain rfl | hk := le_succ_iff_eq_or_le.mp hk
    · simp [InverseSystem.map_self]
    · funext l
      rw [piEquivSucc]; rw [piSplitLE_lt (lt_succ hk)]; rw [← InverseSystem.map_map (f := f) hk (le_succ i)]; rw [← H]; rw [piLTProj]; rw [nat le_rfl]
      simp [piSplitLE_lt (l.2.trans_le hk)]
  · rw [piEquivSucc, piSplitLE_lt (h.trans_lt <| lt_succ hj), nat hj, piSplitLE_lt (lt_succ hj)]

end Succ

section Lim

variable {equiv : forall j : Iio i, F j ≃ piLT X j} (nat : IsNatEquiv f equiv)

/--
Definition of `invLimEquiv` / `invLimEquiv` 的定义

English:
definition invLimEquiv
  signature: : limit f i ≃ limit (piLTProj (X := X)) i where
  body: ⟨fun l => equiv l (t.1 l), fun _ _ h => Eq.symm by simp_rw [← t.2 h]; apply nat⟩
  invFun t := ⟨fun l => (equiv l).symm (t.1 l),
fun _ _ h => (Equiv.eq_symm_apply _).mpr by rw [nat, ← t.2 h] <;> simp⟩
  left_inv t := by ext; apply Equiv.left_inv
  right_inv t := by ext1; ext1; apply Equiv.right_inv

中文:
定义 invLimEquiv
  签名: : limit f i ≃ limit (piLTProj (X := X)) i where
  定义体: ⟨fun l => equiv l (t.1 l), fun _ _ h => Eq.symm by simp_rw [← t.2 h]; apply nat⟩
  invFun t := ⟨fun l => (equiv l).symm (t.1 l),
fun _ _ h => (Equiv.eq_symm_apply _).mpr by rw [nat, ← t.2 h] <;> simp⟩
  left_inv t := by ext; apply Equiv.left_inv
  right_inv t := by ext1; ext1; apply Equiv.right_inv
-/
@[simps] def invLimEquiv : limit f i ≃ limit (piLTProj (X := X)) i where
toFun t := ⟨fun l => equiv l (t.1 l), fun _ _ h => Eq.symm by simp_rw [← t.2 h]; apply nat⟩
  invFun t := ⟨fun l => (equiv l).symm (t.1 l),
fun _ _ h => (Equiv.eq_symm_apply _).mpr by rw [nat, ← t.2 h] <;> simp⟩
  left_inv t := by ext; apply Equiv.left_inv
  right_inv t := by ext1; ext1; apply Equiv.right_inv

variable (equivLim : F i ≃ limit f i) (hi : IsSuccPrelimit i)

/--
Definition of `piEquivLim` / `piEquivLim` 的定义

English:
definition piEquivLim
  signature: : forall j : Iic i, F j ≃ piLT X j
  body: piSplitLE (X := fun j => F j ≃ piLT X j)
    (equiv, equivLim.trans <| (invLimEquiv nat).trans (piLTLim hi).symm)

中文:
定义 piEquivLim
  签名: : 对任意 j : 左无界右闭区间 i, F j ≃ piLT X j
  定义体: piSplitLE (X := fun j => F j ≃ piLT X j)
    (equiv, equivLim.trans <| (invLimEquiv nat).trans (piLTLim hi).symm)

Depends on / 依赖: equivLim, equivLim.trans, invLimEquiv, piLTLim, piSplitLE
-/
noncomputable def piEquivLim : forall j : Iic i, F j ≃ piLT X j :=
  piSplitLE (X := fun j => F j ≃ piLT X j)
    (equiv, equivLim.trans <| (invLimEquiv nat).trans (piLTLim hi).symm)

variable {equivLim}
/--
theorem `isNatEquiv_piEquivLim` / 定理 `isNatEquiv_piEquivLim`

English:
theorem isNatEquiv_piEquivLim
  given: [InverseSystem f] (H : forall x l, (equivLim x).1 l = f l.2.le x)
  proof: fun j k hj hk h t => by
  obtain rfl | hj := hj.eq_or_lt
  · obtain rfl | hk := hk.eq_or_lt
    · simp [InverseSystem.map_self]
    · funext l
      simp_rw [piEquivLim, piSplitLE_lt hk, piSplitLE_eq, Equiv.trans_apply]
      rw [piLTProj]; rw [piLTLim_symm_apply hi ⟨k]; rw [hk⟩ (by exact l.2)]; rw [invLimEquiv_apply_coe]; rw [H]
  · rw [piEquivLim, piSplitLE_lt (h.trans_lt hj), piSplitLE_lt hj]; apply nat

中文:
定理 is自然数Equiv_piEquivLim
  条件: [InverseSystem f] (H : 对任意 x l, (equivLim x).1 l = f l.2.le x)
  证明: fun j k hj hk h t => by
  obtain rfl | hj := hj.eq_or_lt
  · obtain rfl | hk := hk.eq_or_lt
    · simp [InverseSystem.map_self]
    · funext l
      simp_rw [piEquivLim, piSplitLE_lt hk, piSplitLE_eq, Equiv.trans_apply]
      rw [piLTProj]; rw [piLTLim_symm_apply hi ⟨k]; rw [hk⟩ (by exact l.2)]; rw [invLimEquiv_apply_coe]; rw [H]
  · rw [piEquivLim, piSplitLE_lt (h.trans_lt hj), piSplitLE_lt hj]; apply nat

Depends on / 依赖: Equiv.trans_apply, InverseSystem, InverseSystem.map_self, eq_or_lt, h.trans_lt, hj.eq_or_lt, hk.eq_or_lt, invLimEquiv_apply_coe, map_self, piEquivLim, piLTLim_symm_apply, piLTProj, piSplitLE_eq, piSplitLE_lt, simp_rw, trans_apply, trans_lt
-/
theorem isNatEquiv_piEquivLim [InverseSystem f] (H : forall x l, (equivLim x).1 l = f l.2.le x) :
    IsNatEquiv f (piEquivLim nat equivLim hi) := fun j k hj hk h t => by
  obtain rfl | hj := hj.eq_or_lt
  · obtain rfl | hk := hk.eq_or_lt
    · simp [InverseSystem.map_self]
    · funext l
      simp_rw [piEquivLim, piSplitLE_lt hk, piSplitLE_eq, Equiv.trans_apply]
      rw [piLTProj]; rw [piLTLim_symm_apply hi ⟨k]; rw [hk⟩ (by exact l.2)]; rw [invLimEquiv_apply_coe]; rw [H]
  · rw [piEquivLim, piSplitLE_lt (h.trans_lt hj), piSplitLE_lt hj]; apply nat

end Lim

section Unique

variable [SuccOrder ι] (f) (equivSucc : forall ⦃i⦄, ¬IsMax i -> F i⁺ ≃ F i × X i)

/--
Definition of `PEquivOn` / `PEquivOn` 的定义

English:
structure PEquivOn
  parameters: (s : Set ι)
  axioms and operations (3):
    - equiv((i : s)) : F i ≃ piLT X i
    - nat : IsNatEquiv f equiv
    - compat({i : ι} (hsi : (i⁺ : ι) in s) (hi : ¬IsMax i) (x)) : equiv ⟨i⁺, hsi⟩ x ⟨i, lt_succ_of_not_isMax hi⟩ = (equivSucc hi x).2

中文:
结构 PEquivOn
  参数: (s : 集合 ι)
  公理与运算 (3 个):
    - equiv((i : s)) : F i ≃ piLT X i
    - nat : Is自然数Equiv f equiv
    - compat({i : ι} (hsi : (i⁺ : ι) in s) (hi : ¬IsMax i) (x)) : equiv ⟨i⁺, hsi⟩ x ⟨i, lt_succ_of_not_isMax hi⟩ = (equivSucc hi x).2
-/
@[ext] structure PEquivOn (s : Set ι) where
  /-- A partial family of bijections between `F` and `piLT X` defined on some set in `ι`. -/
  equiv (i : s) : F i ≃ piLT X i
  /-- It is a natural family of bijections. -/
  nat : IsNatEquiv f equiv
  /-- It is compatible with a family of bijections relating `F i⁺` to `F i`. -/
  compat {i : ι} (hsi : (i⁺ : ι) in s) (hi : ¬IsMax i) (x) :
    equiv ⟨i⁺, hsi⟩ x ⟨i, lt_succ_of_not_isMax hi⟩ = (equivSucc hi x).2

variable {s t : Set ι} {f equivSucc} [WellFoundedLT ι]

/--
Definition of `PEquivOn.restrict` / `PEquivOn.restrict` 的定义

English:
definition PEquivOn.restrict
  signature: (e : PEquivOn f equivSucc t) (h : s subseteq t)
  body: e.equiv ⟨i, h i.2⟩
  nat _ _ _ _ := e.nat _ _
  compat _ := e.compat _

中文:
定义 PEquivOn.restrict
  签名: (e : PEquivOn f equivSucc t) (h : s subseteq t)
  定义体: e.equiv ⟨i, h i.2⟩
  nat _ _ _ _ := e.nat _ _
  compat _ := e.compat _
-/
@[simps] def PEquivOn.restrict (e : PEquivOn f equivSucc t) (h : s subseteq t) :
    PEquivOn f equivSucc s where
  equiv i := e.equiv ⟨i, h i.2⟩
  nat _ _ _ _ := e.nat _ _
  compat _ := e.compat _

/--
theorem `unique_pEquivOn` / 定理 `unique_pEquivOn`

English:
theorem unique_pEquivOn
  given: (hs : IsLowerSet s) {e₁ e₂ : PEquivOn f equivSucc s}
  statement: e₁ = e₂
  proof: by
  obtain ⟨e₁, nat₁, compat₁⟩ := e₁
  obtain ⟨e₂, nat₂, compat₂⟩ := e₂
  ext1; ext1 i; dsimp only
  refine SuccOrder.prelimitRecOn i.1 (motive := fun i => forall h : i in s, e₁ ⟨i, h⟩ = e₂ ⟨i, h⟩)
    (fun i nmax ih hi => ?_) (fun i lim ih hi => ?_) i.2
  · ext x ⟨j, hj⟩
    obtain rfl | hj := ((lt_succ_iff_of_not_isMax nmax).mp hj).eq_or_lt
    · exact (compat₁ _ nmax x).trans (compat₂ _ nmax x).symm
    have hi : i in s := hs (le_succ i) hi
    rw [piLTProj_intro (f := e₁ _ x) (le_succ i) (by exact hj)]; rw [← nat₁ _ hi (by exact le_succ i)]; rw [ih]; rw [nat₂ _ hi (by exact le_succ i)]
  · ext x j
    have ⟨k, hjk, hki⟩ := lim.mid j.2
    have hk : k in s := hs hki.le hi
    rw [piLTProj_intro (f := e₁ _ x) hki.le hjk]; rw [piLTProj_intro (f := e₂ _ x) hki.le hjk]; rw [← nat₁ _ hk]; rw [← nat₂ _ hk]; rw [ih _ hki]

中文:
定理 unique_pEquivOn
  条件: (hs : 是下集 s) {e₁ e₂ : PEquivOn f equivSucc s}
  结论: e₁ = e₂
  证明: by
  obtain ⟨e₁, nat₁, compat₁⟩ := e₁
  obtain ⟨e₂, nat₂, compat₂⟩ := e₂
  ext1; ext1 i; dsimp only
  refine SuccOrder.prelimitRecOn i.1 (motive := fun i => forall h : i in s, e₁ ⟨i, h⟩ = e₂ ⟨i, h⟩)
    (fun i nmax ih hi => ?_) (fun i lim ih hi => ?_) i.2
  · ext x ⟨j, hj⟩
    obtain rfl | hj := ((lt_succ_iff_of_not_isMax nmax).mp hj).eq_or_lt
    · exact (compat₁ _ nmax x).trans (compat₂ _ nmax x).symm
    have hi : i in s := hs (le_succ i) hi
    rw [piLTProj_intro (f := e₁ _ x) (le_succ i) (by exact hj)]; rw [← nat₁ _ hi (by exact le_succ i)]; rw [ih]; rw [nat₂ _ hi (by exact le_succ i)]
  · ext x j
    have ⟨k, hjk, hki⟩ := lim.mid j.2
    have hk : k in s := hs hki.le hi
    rw [piLTProj_intro (f := e₁ _ x) hki.le hjk]; rw [piLTProj_intro (f := e₂ _ x) hki.le hjk]; rw [← nat₁ _ hk]; rw [← nat₂ _ hk]; rw [ih _ hki]

Depends on / 依赖: SuccOrder, SuccOrder.prelimitRecOn, eq_or_lt, le_succ, lt_succ_iff_of_not_isMax, motive, piLTProj_intro, prelimitRecOn
-/
theorem unique_pEquivOn (hs : IsLowerSet s) {e₁ e₂ : PEquivOn f equivSucc s} : e₁ = e₂ := by
  obtain ⟨e₁, nat₁, compat₁⟩ := e₁
  obtain ⟨e₂, nat₂, compat₂⟩ := e₂
  ext1; ext1 i; dsimp only
  refine SuccOrder.prelimitRecOn i.1 (motive := fun i => forall h : i in s, e₁ ⟨i, h⟩ = e₂ ⟨i, h⟩)
    (fun i nmax ih hi => ?_) (fun i lim ih hi => ?_) i.2
  · ext x ⟨j, hj⟩
    obtain rfl | hj := ((lt_succ_iff_of_not_isMax nmax).mp hj).eq_or_lt
    · exact (compat₁ _ nmax x).trans (compat₂ _ nmax x).symm
    have hi : i in s := hs (le_succ i) hi
    rw [piLTProj_intro (f := e₁ _ x) (le_succ i) (by exact hj)]; rw [← nat₁ _ hi (by exact le_succ i)]; rw [ih]; rw [nat₂ _ hi (by exact le_succ i)]
  · ext x j
    have ⟨k, hjk, hki⟩ := lim.mid j.2
    have hk : k in s := hs hki.le hi
    rw [piLTProj_intro (f := e₁ _ x) hki.le hjk]; rw [piLTProj_intro (f := e₂ _ x) hki.le hjk]; rw [← nat₁ _ hk]; rw [← nat₂ _ hk]; rw [ih _ hki]

/--
theorem `pEquivOn_apply_eq` / 定理 `pEquivOn_apply_eq`

English:
theorem pEquivOn_apply_eq
  statement: (h : IsLowerSet (s inter t))
  proof: show (e₁.restrict inter_subset_left).equiv ⟨i, his, hit⟩ =
       (e₂.restrict inter_subset_right).equiv ⟨i, his, hit⟩ from
  congr_fun (congr_arg _ <| unique_pEquivOn h) _

中文:
定理 pEquivOn_apply_eq
  结论: (h : 是下集 (s inter t))
  证明: show (e₁.restrict inter_subset_left).equiv ⟨i, his, hit⟩ =
       (e₂.restrict inter_subset_right).equiv ⟨i, his, hit⟩ from
  congr_fun (congr_arg _ <| unique_pEquivOn h) _

Depends on / 依赖: congr_arg, congr_fun, inter_subset_left, inter_subset_right, restrict, unique_pEquivOn
-/
theorem pEquivOn_apply_eq (h : IsLowerSet (s inter t))
    {e₁ : PEquivOn f equivSucc s} {e₂ : PEquivOn f equivSucc t} {i} {his : i in s} {hit : i in t} :
    e₁.equiv ⟨i, his⟩ = e₂.equiv ⟨i, hit⟩ :=
  show (e₁.restrict inter_subset_left).equiv ⟨i, his, hit⟩ =
       (e₂.restrict inter_subset_right).equiv ⟨i, his, hit⟩ from
  congr_fun (congr_arg _ <| unique_pEquivOn h) _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `pEquivOnSucc` / `pEquivOnSucc` 的定义

English:
definition pEquivOnSucc
  signature: [InverseSystem f] (hi : ¬IsMax i) (e : PEquivOn f equivSucc (Iic i))
  body: piEquivSucc e.equiv (equivSucc hi) hi
  nat := isNatEquiv_piEquivSucc hi (H hi) e.nat
  compat hsj hj x := by
    obtain eq | lt := hsj.eq_or_lt
    · cases (succ_eq_succ_iff_of_not_isMax hj hi).mp eq; simp [piEquivSucc]
    · rwa [piEquivSucc, piSplitLE_lt, e.compat]

中文:
定义 pEquivOnSucc
  签名: [InverseSystem f] (hi : ¬IsMax i) (e : PEquivOn f equivSucc (左无界右闭区间 i))
  定义体: piEquivSucc e.equiv (equivSucc hi) hi
  nat := isNatEquiv_piEquivSucc hi (H hi) e.nat
  compat hsj hj x := by
    obtain eq | lt := hsj.eq_or_lt
    · cases (succ_eq_succ_iff_of_not_isMax hj hi).mp eq; simp [piEquivSucc]
    · rwa [piEquivSucc, piSplitLE_lt, e.compat]

Depends on / 依赖: e.equiv, equivSucc, piEquivSucc
-/
def pEquivOnSucc [InverseSystem f] (hi : ¬IsMax i) (e : PEquivOn f equivSucc (Iic i))
    (H : forall ⦃i⦄ (hi : ¬ IsMax i) x, (equivSucc hi x).1 = f (le_succ i) x) :
    PEquivOn f equivSucc (Iic i⁺) where
  equiv := piEquivSucc e.equiv (equivSucc hi) hi
  nat := isNatEquiv_piEquivSucc hi (H hi) e.nat
  compat hsj hj x := by
    obtain eq | lt := hsj.eq_or_lt
    · cases (succ_eq_succ_iff_of_not_isMax hj hi).mp eq; simp [piEquivSucc]
    · rwa [piEquivSucc, piSplitLE_lt, e.compat]

variable (hi : IsSuccPrelimit i) (e : forall j : Iio i, PEquivOn f equivSucc (Iic j))

/--
Definition of `pEquivOnGlue` / `pEquivOnGlue` 的定义

English:
definition pEquivOnGlue
  signature: : PEquivOn f equivSucc (Iio i) where
  body: (piLTLim (X := fun j => F j ≃ piLT X j) hi).symm
    ⟨fun j => ((e j).restrict fun _ h => h.le).equiv, fun _ _ h => funext fun _ =>
      pEquivOn_apply_eq ((isLowerSet_Iio _).inter <| isLowerSet_Iio _)⟩
  nat j k hj hk h := by rw [piLTLim_symm_apply]; exacts [(e _).nat _ _ _, h.trans_lt (hi.mid _).2.1]
  compat hj := have k := hi.mid hj
    by rw [piLTLim_symm_apply hi ⟨_, k.2.2⟩ (by exact k.2.1)]; apply (e _).compat

中文:
定义 pEquivOnGlue
  签名: : PEquivOn f equivSucc (左无界右开区间 i) where
  定义体: (piLTLim (X := fun j => F j ≃ piLT X j) hi).symm
    ⟨fun j => ((e j).restrict fun _ h => h.le).equiv, fun _ _ h => funext fun _ =>
      pEquivOn_apply_eq ((isLowerSet_Iio _).inter <| isLowerSet_Iio _)⟩
  nat j k hj hk h := by rw [piLTLim_symm_apply]; exacts [(e _).nat _ _ _, h.trans_lt (hi.mid _).2.1]
  compat hj := have k := hi.mid hj
    by rw [piLTLim_symm_apply hi ⟨_, k.2.2⟩ (by exact k.2.1)]; apply (e _).compat

Depends on / 依赖: piLTLim
-/
noncomputable def pEquivOnGlue : PEquivOn f equivSucc (Iio i) where
  equiv := (piLTLim (X := fun j => F j ≃ piLT X j) hi).symm
    ⟨fun j => ((e j).restrict fun _ h => h.le).equiv, fun _ _ h => funext fun _ =>
      pEquivOn_apply_eq ((isLowerSet_Iio _).inter <| isLowerSet_Iio _)⟩
  nat j k hj hk h := by rw [piLTLim_symm_apply]; exacts [(e _).nat _ _ _, h.trans_lt (hi.mid _).2.1]
  compat hj := have k := hi.mid hj
    by rw [piLTLim_symm_apply hi ⟨_, k.2.2⟩ (by exact k.2.1)]; apply (e _).compat

/--
Definition of `pEquivOnLim` / `pEquivOnLim` 的定义

English:
definition pEquivOnLim
  signature: [InverseSystem f]
  body: piEquivLim (pEquivOnGlue hi e).nat equivLim hi
  nat := isNatEquiv_piEquivLim (pEquivOnGlue hi e).nat hi H
  compat hsj hj x := by
    rw [piEquivLim]; rw [piSplitLE_lt (hi.succ_lt <| (succ_le_iff_of_not_isMax hj).mp hsj)]
    apply (pEquivOnGlue hi e).compat

中文:
定义 pEquivOnLim
  签名: [InverseSystem f]
  定义体: piEquivLim (pEquivOnGlue hi e).nat equivLim hi
  nat := isNatEquiv_piEquivLim (pEquivOnGlue hi e).nat hi H
  compat hsj hj x := by
    rw [piEquivLim]; rw [piSplitLE_lt (hi.succ_lt <| (succ_le_iff_of_not_isMax hj).mp hsj)]
    apply (pEquivOnGlue hi e).compat

Depends on / 依赖: equivLim, pEquivOnGlue, piEquivLim
-/
noncomputable def pEquivOnLim [InverseSystem f]
    (equivLim : F i ≃ limit f i) (H : forall x l, (equivLim x).1 l = f l.2.le x) :
    PEquivOn f equivSucc (Iic i) where
  equiv := piEquivLim (pEquivOnGlue hi e).nat equivLim hi
  nat := isNatEquiv_piEquivLim (pEquivOnGlue hi e).nat hi H
  compat hsj hj x := by
    rw [piEquivLim]; rw [piSplitLE_lt (hi.succ_lt <| (succ_le_iff_of_not_isMax hj).mp hsj)]
    apply (pEquivOnGlue hi e).compat

end Unique

variable [WellFoundedLT ι] [SuccOrder ι] [InverseSystem f]
  (equivSucc : forall i, ¬IsMax i -> {e : F i⁺ ≃ F i × X i // forall x, (e x).1 = f (le_succ i) x})
  (equivLim : forall i, IsSuccPrelimit i -> {e : F i ≃ limit f i // forall x l, (e x).1 l = f l.2.le x})

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def globalEquivAux (i : ι)
  body: SuccOrder.prelimitRecOn i
    (fun _ hi e => pEquivOnSucc hi e fun i hi => (equivSucc i hi).2)
    fun i hi e => pEquivOnLim hi (fun j => e j j.2) (equivLim i hi).1 (equivLim i hi).2

中文:
定义 noncomputable
  签名: def globalEquivAux (i : ι)
  定义体: SuccOrder.prelimitRecOn i
    (fun _ hi e => pEquivOnSucc hi e fun i hi => (equivSucc i hi).2)
    fun i hi e => pEquivOnLim hi (fun j => e j j.2) (equivLim i hi).1 (equivLim i hi).2
-/
private noncomputable def globalEquivAux (i : ι) :
    PEquivOn f (fun i hi => (equivSucc i hi).1) (Iic i) :=
  SuccOrder.prelimitRecOn i
    (fun _ hi e => pEquivOnSucc hi e fun i hi => (equivSucc i hi).2)
    fun i hi e => pEquivOnLim hi (fun j => e j j.2) (equivLim i hi).1 (equivLim i hi).2

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `globalEquiv` / `globalEquiv` 的定义

English:
definition globalEquiv
  signature: (i : ι)
  body: (globalEquivAux equivSucc equivLim i).equiv ⟨i, le_rfl⟩

中文:
定义 globalEquiv
  签名: (i : ι)
  定义体: (globalEquivAux equivSucc equivLim i).equiv ⟨i, le_rfl⟩

Depends on / 依赖: equivLim, equivSucc, globalEquivAux, le_rfl
-/
noncomputable def globalEquiv (i : ι) : F i ≃ piLT X i :=
  (globalEquivAux equivSucc equivLim i).equiv ⟨i, le_rfl⟩

/--
theorem `globalEquiv_naturality` / 定理 `globalEquiv_naturality`

English:
theorem globalEquiv_naturality
  given: ⦃i j⦄ (h : i <= j) (x : F j)
  proof: globalEquiv equivSucc equivLim
    e i (f h x) = piLTProj h (e j x) := by
  refine (DFunLike.congr_fun ?_ _).trans ((globalEquivAux equivSucc equivLim j).nat le_rfl h h x)
  exact pEquivOn_apply_eq ((isLowerSet_Iic _).inter <| isLowerSet_Iic _)

中文:
定理 globalEquiv_naturality
  条件: ⦃i j⦄ (h : i <= j) (x : F j)
  证明: globalEquiv equivSucc equivLim
    e i (f h x) = piLTProj h (e j x) := by
  refine (DFunLike.congr_fun ?_ _).trans ((globalEquivAux equivSucc equivLim j).nat le_rfl h h x)
  exact pEquivOn_apply_eq ((isLowerSet_Iic _).inter <| isLowerSet_Iic _)

Depends on / 依赖: equivLim, equivSucc, globalEquiv
-/
theorem globalEquiv_naturality ⦃i j⦄ (h : i <= j) (x : F j) :
    letI e := globalEquiv equivSucc equivLim
    e i (f h x) = piLTProj h (e j x) := by
  refine (DFunLike.congr_fun ?_ _).trans ((globalEquivAux equivSucc equivLim j).nat le_rfl h h x)
  exact pEquivOn_apply_eq ((isLowerSet_Iic _).inter <| isLowerSet_Iic _)

/--
theorem `globalEquiv_compatibility` / 定理 `globalEquiv_compatibility`

English:
theorem globalEquiv_compatibility
  given: ⦃i⦄ (hi : ¬IsMax i) (x)
  proof: (globalEquivAux equivSucc equivLim i⁺).compat le_rfl hi x

中文:
定理 globalEquiv_compatibility
  条件: ⦃i⦄ (hi : ¬IsMax i) (x)
  证明: (globalEquivAux equivSucc equivLim i⁺).compat le_rfl hi x

Depends on / 依赖: compat, equivLim, equivSucc, globalEquivAux, le_rfl
-/
theorem globalEquiv_compatibility ⦃i⦄ (hi : ¬IsMax i) (x) :
    globalEquiv equivSucc equivLim i⁺ x ⟨i, lt_succ_of_not_isMax hi⟩ = ((equivSucc i hi).1 x).2 :=
  (globalEquivAux equivSucc equivLim i⁺).compat le_rfl hi x

end InverseSystem
