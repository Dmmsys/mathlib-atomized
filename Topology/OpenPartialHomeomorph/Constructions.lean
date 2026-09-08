/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
/-!
# Constructions of new partial homeomorphisms from old

## Main definitions

* `OpenPartialHomeomorph.const`: an open partial homeomorphism which is a constant map,
  whose source and target are necessarily singleton sets
* `OpenPartialHomeomorph.subtypeRestr`: restriction to a subtype
* `OpenPartialHomeomorph.prod`: the product of two open partial homeomorphisms,
  as an open partial homeomorphism on the product space
* `OpenPartialHomeomorph.pi`: the product of a finite family of open partial homeomorphisms
* `OpenPartialHomeomorph.disjointUnion`: combine two open partial homeomorphisms with disjoint
  sources and disjoint targets
* `OpenPartialHomeomorph.lift_openEmbedding`: extend an open partial homeomorphism `X → Y`
  under an open embedding `X → X'`, to an open partial homeomorphism `X' → Z`.
  (This is used to define the disjoint union of charted spaces.)
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-!
## Constants

`PartialEquiv.const` as an open partial homeomorphism
-/
section const

variable {a : X} {b : Y}

/--
This is `PartialEquiv.single` as an open partial homeomorphism: a constant map,
whose source and target are necessarily singleton sets.
-/
/-
**OpenPartialHomeomorph.const** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：const (ha : IsOpen {a}) (hb : IsOpen {b}) : OpenPartialHomeomorph X Y wher
e toPartialEquiv
参数：ha : IsOpen {a}；hb : IsOpen {b}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is `PartialEquiv.single` as an open partial homeomorphism: a constant map,
whose source and target are necessarily singleton sets.
-/
def const (ha : IsOpen {a}) (hb : IsOpen {b}) : OpenPartialHomeomorph X Y where
  toPartialEquiv := PartialEquiv.single a b
  open_source := ha
  open_target := hb
  continuousOn_toFun := by simp
  continuousOn_invFun := by simp

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.const_apply** 是 Mathlib 中的一个引理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：const_apply (ha : IsOpen {a}) (hb : IsOpen {b}) (x : X) : (const ha hb) x 
= b
参数：ha : IsOpen {a}；hb : IsOpen {b}；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_apply (ha : IsOpen {a}) (hb : IsOpen {b}) (x : X) : (const ha hb) x = b := rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.const_source** 是 Mathlib 中的一个引理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：const_source (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).source = 
{a}
参数：ha : IsOpen {a}；hb : IsOpen {b}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_source (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).source = {a} := rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.const_target** 是 Mathlib 中的一个引理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：const_target (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).target = 
{b}
参数：ha : IsOpen {a}；hb : IsOpen {b}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_target (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).target = {b} := rfl

end const

/-!
## Products

Product of two open partial homeomorphisms
-/
section Prod

/-- The product of two open partial homeomorphisms, as an open partial homeomorphism on the product
space. -/
@[simps! (attr := mfld_simps) -fullyApplied toPartialHomeomorph apply,
  simps! -isSimp source target symm_apply]
/-
**OpenPartialHomeomorph.prod** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：prod (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
 OpenPartialHomeomorph (X × Y) (X' × Y') where open_source
参数：eX : OpenPartialHomeomorph X X'；eY : OpenPartialHomeomorph Y Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prod (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
    OpenPartialHomeomorph (X × Y) (X' × Y') where
  open_source := eX.open_source.prod eY.open_source
  open_target := eX.open_target.prod eY.open_target
  continuousOn_toFun := eX.continuousOn.prodMap eY.continuousOn
  continuousOn_invFun := eX.continuousOn_symm.prodMap eY.continuousOn_symm
  toPartialEquiv := eX.toPartialEquiv.prod eY.toPartialEquiv

@[deprecated "deprecated in favour of `OpenPartialHomeomorph.prod_toPartialHomeomorph`"
  (since := "2026-06-24")]
/-
**OpenPartialHomeomorph.prod_toPartialEquiv** 是 Mathlib 中的一个引理，位于命名空间 `OpenParti
alHomeomorph`。
形式化陈述：prod_toPartialEquiv (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHom
eomorph Y Y') : (eX.prod eY).toPartialHomeomorph.toPartialEquiv = eX.toPartialEq
uiv.prod eY.toPartialEquiv
参数：eX : OpenPartialHomeomorph X X'；eY : OpenPartialHomeomorph Y Y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_toPartialEquiv (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
    (eX.prod eY).toPartialHomeomorph.toPartialEquiv = eX.toPartialEquiv.prod eY.toPartialEquiv :=
  rfl
@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.prod_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomor
ph`。
形式化陈述：prod_symm (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y 
Y') : (eX.prod eY).symm = eX.symm.prod eY.symm
参数：eX : OpenPartialHomeomorph X X'；eY : OpenPartialHomeomorph Y Y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_symm (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
    (eX.prod eY).symm = eX.symm.prod eY.symm :=
  rfl

@[simp]
/-
**OpenPartialHomeomorph.refl_prod_refl** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph`。
形式化陈述：refl_prod_refl : (OpenPartialHomeomorph.refl X).prod (OpenPartialHomeomorp
h.refl Y) = OpenPartialHomeomorph.refl (X × Y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.ext`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y]   (e e' : OpenPartialHomeomorph X Y
),   (∀ (x : X)…
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
-/
theorem refl_prod_refl : (OpenPartialHomeomorph.refl X).prod (OpenPartialHomeomorph.refl Y) =
    OpenPartialHomeomorph.refl (X × Y) :=
  OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.prod_trans** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：prod_trans (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph Y Z)
 (e' : OpenPartialHomeomorph X' Y') (f' : OpenPartialHomeomorph Y' Z') : (e.prod
 e').trans (f.prod f') = (e.trans f).prod (e'.trans f')
参数：e : OpenPartialHomeomorph X Y；f : OpenPartialHomeomorph Y Z；e' : OpenPartialH
omeomorph X' Y'；f' : OpenPartialHomeomorph Y' Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialEquiv_injective`：toPartialEquiv_injective
 : Injective (fun f => f.toPartialEquiv : OpenPartialHomeomorph X Y -> PartialEq
uiv X Y)
· 使用定理 `PartialEquiv.prod_trans`：prod_trans {η : Type*} {ε : Type*} (e : Partial
Equiv α β) (f : PartialEquiv β γ) (e' : PartialEquiv δ η) (f' : PartialEquiv η ε
) : (e.prod e…
-/
theorem prod_trans (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph Y Z)
    (e' : OpenPartialHomeomorph X' Y') (f' : OpenPartialHomeomorph Y' Z') :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
  toPartialEquiv_injective <| e.1.prod_trans ..
/-
**OpenPartialHomeomorph.prod_eq_prod_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：prod_eq_prod_of_nonempty {eX eX' : OpenPartialHomeomorph X X'} {eY eY' : O
penPartialHomeomorph Y Y'} (h : (eX.prod eY).source.Nonempty) : eX.prod eY = eX'
.prod eY' ↔ eX = eX' ∧ eY = eY'
参数：h : (eX.prod eY).source.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OpenPartialHomeomorph.prod_apply`：∀ {X : Type u_1} {X' : Type u_2} {Y : 
Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce X'] [inst_2 : Topol…
· 使用定理 `OpenPartialHomeomorph.prod_symm_apply`：∀ {X : Type u_1} {X' : Type u_2} 
{Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : Topologic
alSpace X'] [inst_2 : Topol…
· 使用定理 `OpenPartialHomeomorph.prod_source`：∀ {X : Type u_1} {X' : Type u_2} {Y :
 Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : TopologicalSp
ace X'] [inst_2 : Topol…
· 使用定理 `Set.prod_eq_prod_iff_of_nonempty`：prod_eq_prod_iff_of_nonempty (h : (s ×
ˢ t).Nonempty) : s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_prod_of_nonempty {eX eX' : OpenPartialHomeomorph X X'}
    {eY eY' : OpenPartialHomeomorph Y Y'} (h : (eX.prod eY).source.Nonempty) :
    eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  have : Nonempty X := ⟨x⟩
  have : Nonempty X' := ⟨eX x⟩
  have : Nonempty Y := ⟨y⟩
  have : Nonempty Y' := ⟨eY y⟩
  simp_rw [OpenPartialHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const,
    and_assoc, and_left_comm]
/-
**OpenPartialHomeomorph.prod_eq_prod_of_nonempty'** 是 Mathlib 中的一个定理，位于命名空间 `Ope
nPartialHomeomorph`。
形式化陈述：prod_eq_prod_of_nonempty' {eX eX' : OpenPartialHomeomorph X X'} {eY eY' : 
OpenPartialHomeomorph Y Y'} (h : (eX'.prod eY').source.Nonempty) : eX.prod eY = 
eX'.prod eY' ↔ eX = eX' ∧ eY = eY'
参数：h : (eX'.prod eY').source.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `OpenPartialHomeomorph.prod_eq_prod_of_nonempty`：prod_eq_prod_of_nonempty
 {eX eX' : OpenPartialHomeomorph X X'} {eY eY' : OpenPartialHomeomorph Y Y'} (h 
: (eX.prod eY).source.Nonempty) : eX…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_eq_prod_of_nonempty'
    {eX eX' : OpenPartialHomeomorph X X'} {eY eY' : OpenPartialHomeomorph Y Y'}
    (h : (eX'.prod eY').source.Nonempty) : eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ eY']
/-
**OpenPartialHomeomorph.prod_symm_trans_prod** 是 Mathlib 中的一个定理，位于命名空间 `OpenPart
ialHomeomorph`。
形式化陈述：prod_symm_trans_prod (e f : OpenPartialHomeomorph X Y) (e' f' : OpenPartia
lHomeomorph X' Y') : (e.prod e').symm.trans (f.prod f') = (e.symm.trans f).prod 
(e'.symm.trans f')
参数：e f : OpenPartialHomeomorph X Y；e' f' : OpenPartialHomeomorph X' Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.prod_trans`：prod_trans (e : OpenPartialHomeomorph 
X Y) (f : OpenPartialHomeomorph Y Z) (e' : OpenPartialHomeomorph X' Y') (f' : Op
enPartialHomeomorph Y'…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_symm_trans_prod
    (e f : OpenPartialHomeomorph X Y) (e' f' : OpenPartialHomeomorph X' Y') :
    (e.prod e').symm.trans (f.prod f') = (e.symm.trans f).prod (e'.symm.trans f') := by
  simp

end Prod

/-!
## Pi types

Finite indexed products of partial homeomorphisms
-/
section Pi

variable {ι : Type*} [Finite ι] {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)] (ei : ∀ i, OpenPartialHomeomorph (X i) (Y i))

/-- The product of a finite family of `OpenPartialHomeomorph`s. -/
@[simps! toPartialHomeomorph apply symm_apply]
/-
**OpenPartialHomeomorph.pi** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：pi : OpenPartialHomeomorph (forall i, X i) (forall i, Y i) where toPartial
Equiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a finite family of `OpenPartialHomeomorph`s.
-/
def pi : OpenPartialHomeomorph (∀ i, X i) (∀ i, Y i) where
  toPartialEquiv := PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
  continuousOn_invFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn_symm.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial

end Pi

/-!
## Disjoint union

Combining two partial homeomorphisms using `Set.piecewise`
-/
section Piecewise

/-- Combine two `OpenPartialHomeomorph`s using `Set.piecewise`. The source of the new
`OpenPartialHomeomorph` is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly
for target.  The function sends `e.source ∩ s` to `e.target ∩ t` using `e` and
`e'.source \ s` to `e'.target \ t` using `e'`, and similarly for the inverse function.
To ensure the maps `toFun` and `invFun` are inverse of each other on the new `source` and `target`,
the definition assumes that the sets `s` and `t` are related both by `e.is_image` and `e'.is_image`.
To ensure that the new maps are continuous on `source`/`target`, it also assumes that `e.source` and
`e'.source` meet `frontier s` on the same set and `e x = e' x` on this intersection. -/
@[simps! -fullyApplied toPartialHomeomorph apply]
/-
**OpenPartialHomeomorph.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomor
ph`。
形式化陈述：piecewise (e e' : OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y) [fora
ll x, Decidable (x in s)] [forall y, Decidable (y in t)] (H : e.IsImage s t) (H'
 : e'.IsImage s t) (Hs : e.source inter frontier s = e'.source inter frontier s)
 (Heq : EqOn e e' (e.source inter frontier s)) : OpenPartialHomeomorph X Y where
 toPartialEquiv
参数：e e' : OpenPartialHomeomorph X Y；s : Set X；t : Set Y；x in s；y in t；H : e.IsIm
age s t；H' : e'.IsImage s t；Hs : e.source inter frontier s = e'.source inter fro
ntier s；Heq : EqOn e e' (e.source inter frontier s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine two `OpenPartialHomeomorph`s using `Set.piecewise`. The source of the ne
w
`OpenPartialHomeomorph` is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source 
\ s`, and similarly
for target.  The function sends `e.source ∩ s` to `e.target ∩ t` using `e` and
`e'.source \ s` to `e'.target \ t` using `e'`, and similarly for the inverse fun
ction.
To ensure the maps `toFun` and `invFun` are inverse of each other on the new `so
urce` and `target`,
the definition assumes that the sets `s` and `t` are related both by `e.is_image
` and `e'.is_image`.
To ensure that the new maps are continuous on `source`/`target`, it also assumes
 that `e.source` and
`e'.source` meet `frontier s` on the same set and `e x = e' x` on this intersect
ion.
-/
def piecewise (e e' : OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : OpenPartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs Heq
  continuousOn_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq)

@[simp]
/-
**OpenPartialHomeomorph.symm_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph`。
形式化陈述：symm_piecewise (e e' : OpenPartialHomeomorph X Y) {s : Set X} {t : Set Y} 
[forall x, Decidable (x in s)] [forall y, Decidable (y in t)] (H : e.IsImage s t
) (H' : e'.IsImage s t) (Hs : e.source inter frontier s = e'.source inter fronti
er s) (Heq : EqOn e e' (e.source inter frontier s)) : (e.piecewise e' s t H H' H
s Heq).symm = e.symm.piecewise e'.symm t s H.symm H'.symm (H.frontier.inter_eq_o
f_inter_eq_of_eqOn H'.frontier Hs Heq) (H.frontier.symm_eqOn_of_inter_eq_of_eqOn
 Hs Heq)
参数：e e' : OpenPartialHomeomorph X Y；x in s；y in t；H : e.IsImage s t；H' : e'.IsIm
age s t；Hs : e.source inter frontier s = e'.source inter frontier s；Heq : EqOn e
 e' (e.source inter frontier s)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_piecewise (e e' : OpenPartialHomeomorph X Y) {s : Set X} {t : Set Y}
    [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
        (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq) :=
  rfl

/-- Combine two `OpenPartialHomeomorph`s with disjoint sources and disjoint targets. We reuse
`OpenPartialHomeomorph.piecewise` then override `toPartialEquiv` to `PartialEquiv.disjointUnion`.
This way we have better definitional equalities for `source` and `target`. -/
/-
**OpenPartialHomeomorph.disjointUnion** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：disjointUnion (e e' : OpenPartialHomeomorph X Y) [forall x, Decidable (x i
n e.source)] [forall y, Decidable (y in e.target)] (Hs : Disjoint e.source e'.so
urce) (Ht : Disjoint e.target e'.target) : OpenPartialHomeomorph X Y
参数：e e' : OpenPartialHomeomorph X Y；x in e.source；y in e.target；Hs : Disjoint e.
source e'.source；Ht : Disjoint e.target e'.target。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.isImage_source_target`：isImage_source_target : e.I
sImage e.source e.target

--- 原说明 ---
Combine two `OpenPartialHomeomorph`s with disjoint sources and disjoint targets.
 We reuse
`OpenPartialHomeomorph.piecewise` then override `toPartialEquiv` to `PartialEqui
v.disjointUnion`.
This way we have better definitional equalities for `source` and `target`.
-/
def disjointUnion (e e' : OpenPartialHomeomorph X Y) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : OpenPartialHomeomorph X Y :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eqOn_empty _ _)).replacePartialEquiv
    (e.toPartialEquiv.disjointUnion e'.toPartialEquiv Hs Ht)
    (PartialEquiv.disjointUnion_eq_piecewise _ _ _ _).symm

end Piecewise

/-
## Post-composition

Post-composing an `OpenPartialHomeomorph` with a homeomorphism
-/
section transHomeomorph

/-- Postcompose an open partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
/-
**OpenPartialHomeomorph.transHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：transHomeomorph (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) : OpenPartia
lHomeomorph X Z where toPartialEquiv
参数：e : OpenPartialHomeomorph X Y；f' : Y ≃ₜ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
Postcompose an open partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior.
-/
def transHomeomorph (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) : OpenPartialHomeomorph X Z where
  toPartialEquiv := e.toPartialEquiv.transEquiv f'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.preimage f'.symm.continuous
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id
/-
**OpenPartialHomeomorph.transHomeomorph_eq_trans** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：transHomeomorph_eq_trans (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) : e
.transHomeomorph f' = e.trans f'.toOpenPartialHomeomorph
参数：e : OpenPartialHomeomorph X Y；f' : Y ≃ₜ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialEquiv_injective`：toPartialEquiv_injective
 : Injective (fun f => f.toPartialEquiv : OpenPartialHomeomorph X Y -> PartialEq
uiv X Y)
· 使用定理 `PartialEquiv.transEquiv_eq_trans`：transEquiv_eq_trans (e : PartialEquiv 
α β) (e' : β ≃ γ) : e.transEquiv e' = e.trans e'.toPartialEquiv
-/
theorem transHomeomorph_eq_trans (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) :
    e.transHomeomorph f' = e.trans f'.toOpenPartialHomeomorph :=
  toPartialEquiv_injective <| PartialEquiv.transEquiv_eq_trans _ _

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.transHomeomorph_transHomeomorph** 是 Mathlib 中的一个定理，位于命名空
间 `OpenPartialHomeomorph`。
形式化陈述：transHomeomorph_transHomeomorph (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ
 Z) (f'' : Z ≃ₜ Z') : (e.transHomeomorph f').transHomeomorph f'' = e.transHomeom
orph (f'.trans f'')
参数：e : OpenPartialHomeomorph X Y；f' : Y ≃ₜ Z；f'' : Z ≃ₜ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.transHomeomorph_eq_trans`：transHomeomorph_eq_trans
 (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) : e.transHomeomorph f' = e.trans 
f'.toOpenPartialHomeomorph
· 使用定理 `OpenPartialHomeomorph.trans_assoc`：trans_assoc (e'' : OpenPartialHomeomo
rph Z Z') : (e.trans e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `Homeomorph.trans_toOpenPartialHomeomorph`：trans_toOpenPartialHomeomorph 
: (e.trans e').toOpenPartialHomeomorph = e.toOpenPartialHomeomorph.trans e'.toOp
enPartialHomeomorph
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transHomeomorph_transHomeomorph (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z)
    (f'' : Z ≃ₜ Z') :
    (e.transHomeomorph f').transHomeomorph f'' = e.transHomeomorph (f'.trans f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toOpenPartialHomeomorph]

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.trans_transHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：trans_transHomeomorph (e : OpenPartialHomeomorph X Y) (e' : OpenPartialHom
eomorph Y Z) (f'' : Z ≃ₜ Z') : (e.trans e').transHomeomorph f'' = e.trans (e'.tr
ansHomeomorph f'')
参数：e : OpenPartialHomeomorph X Y；e' : OpenPartialHomeomorph Y Z；f'' : Z ≃ₜ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.transHomeomorph_eq_trans`：transHomeomorph_eq_trans
 (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) : e.transHomeomorph f' = e.trans 
f'.toOpenPartialHomeomorph
· 使用定理 `OpenPartialHomeomorph.trans_assoc`：trans_assoc (e'' : OpenPartialHomeomo
rph Z Z') : (e.trans e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_transHomeomorph (e : OpenPartialHomeomorph X Y) (e' : OpenPartialHomeomorph Y Z)
    (f'' : Z ≃ₜ Z') :
    (e.trans e').transHomeomorph f'' = e.trans (e'.transHomeomorph f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc]

end transHomeomorph

/-!
## Restriction to a subtype

`subtypeRestr`: restriction to a subtype
-/
section subtypeRestr

open TopologicalSpace

variable (e : OpenPartialHomeomorph X Y)
variable {s : Opens X} (hs : Nonempty s)

/-- The restriction of an open partial homeomorphism `e` to an open subset `s` of the domain type
produces an open partial homeomorphism whose domain is the subtype `s`. -/
/-
**OpenPartialHomeomorph.subtypeRestr** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：subtypeRestr : OpenPartialHomeomorph s Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of an open partial homeomorphism `e` to an open subset `s` of th
e domain type
produces an open partial homeomorphism whose domain is the subtype `s`.
-/
noncomputable def subtypeRestr : OpenPartialHomeomorph s Y :=
  (s.openPartialHomeomorphSubtypeCoe hs).trans e
/-
**OpenPartialHomeomorph.subtypeRestr_def** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：subtypeRestr_def : e.subtypeRestr hs = (s.openPartialHomeomorphSubtypeCoe 
hs).trans e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeRestr_def : e.subtypeRestr hs = (s.openPartialHomeomorphSubtypeCoe hs).trans e :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.subtypeRestr_coe** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：subtypeRestr_coe : ((e.subtypeRestr hs : OpenPartialHomeomorph s Y) : s ->
 Y) = Set.domRestrict ↑s (e : X -> Y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeRestr_coe :
    ((e.subtypeRestr hs : OpenPartialHomeomorph s Y) : s → Y) = Set.domRestrict ↑s (e : X → Y) :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.subtypeRestr_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenParti
alHomeomorph`。
形式化陈述：subtypeRestr_source : (e.subtypeRestr hs).source = (↑) ⁻¹' e.source
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subtypeRestr_source : (e.subtypeRestr hs).source = (↑) ⁻¹' e.source := by
  simp only [subtypeRestr_def, mfld_simps]
/-
**OpenPartialHomeomorph.map_subtype_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartia
lHomeomorph`。
形式化陈述：map_subtype_source {x : s} (hxe : (x : X) in e.source) : e x in (e.subtype
Restr hs).target
参数：hxe : (x : X) in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target`：openParti
alHomeomorphSubtypeCoe_target : (s.openPartialHomeomorphSubtypeCoe hs).target = 
s
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `OpenPartialHomeomorph.leftInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), Set.LeftInvOn (…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem map_subtype_source {x : s} (hxe : (x : X) ∈ e.source) :
    e x ∈ (e.subtypeRestr hs).target := by
  refine ⟨e.map_source hxe, ?_⟩
  rw [s.openPartialHomeomorphSubtypeCoe_target, mem_preimage, e.leftInvOn hxe]
  exact x.prop
/-
**OpenPartialHomeomorph.subtypeRestr_target_subset** 是 Mathlib 中的一个引理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：subtypeRestr_target_subset (hs : Nonempty s) : (e.subtypeRestr hs).target 
subseteq e.target
参数：hs : Nonempty s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.image_source_eq_target`：image_source_eq_target : e
 '' e.source = e.target
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_source`：subtypeRestr_source : (e.subt
ypeRestr hs).source = (↑) ⁻¹' e.source
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma subtypeRestr_target_subset (hs : Nonempty s) : (e.subtypeRestr hs).target ⊆ e.target := by
  rw [← e.image_source_eq_target, ← OpenPartialHomeomorph.image_source_eq_target,
    e.subtypeRestr_source]
  rintro z ⟨z₀, hz₀, rfl⟩
  use z₀.val
  simpa

/-- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
/-
**OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr** 是 Mathlib 中的一个定理，
位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：subtypeRestr_symm_trans_subtypeRestr (f f' : OpenPartialHomeomorph X Y) : 
(f.subtypeRestr hs).symm.trans (f'.subtypeRestr hs) ≈ (f.symm.trans f').restr (f
.target inter f.symm ⁻¹' s)
参数：f f' : OpenPartialHomeomorph X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage_symm`：isOpen_inter_preimage_
symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target inter e.symm ⁻¹' s)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.ofSet_trans`：ofSet_trans {s : Set X} (hs : IsOpen 
s) : (ofSet s hs).trans e = e.restr s
· 使用定理 `OpenPartialHomeomorph.trans_assoc`：trans_assoc (e'' : OpenPartialHomeomo
rph Z Z') : (e.trans e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `OpenPartialHomeomorph.EqOnSource.trans'`：∀ {X : Type u_1} {Y : Type u_3}
 {Z : Type u_5} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [ins
t_2 : TopologicalSpace Z] {e …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `OpenPartialHomeomorph.ofSet_trans'`：ofSet_trans' {s : Set X} (hs : IsOpe
n s) : (ofSet s hs).trans e = e.restr (e.source inter s)
· 使用定理 `OpenPartialHomeomorph.trans_of_set'`：trans_of_set' {s : Set Y} (hs : IsO
pen s) : e.trans (ofSet s hs) = e.restr (e.source inter e ⁻¹' s)
· 使用定理 `OpenPartialHomeomorph.eqOnSource_refl`：eqOnSource_refl : e ≈ e
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.symm_trans_self`：symm_trans_self : e.symm.trans e 
≈ OpenPartialHomeomorph.ofSet e.target e.open_target
· 使用定理 `TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target`：openParti
alHomeomorphSubtypeCoe_target : (s.openPartialHomeomorphSubtypeCoe hs).target = 
s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.ofSet.congr_simp`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] (s s_1 : Set X) (e_s : s = s_1) (hs : IsOpen s),   OpenPartialHomeo
morph.ofSet s hs = OpenParti…

--- 原说明 ---
This lemma characterizes the transition functions of an open subset in terms of 
the transition
functions of the original space.
-/
theorem subtypeRestr_symm_trans_subtypeRestr (f f' : OpenPartialHomeomorph X Y) :
    (f.subtypeRestr hs).symm.trans (f'.subtypeRestr hs) ≈
      (f.symm.trans f').restr (f.target ∩ f.symm ⁻¹' s) := by
  simp only [subtypeRestr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target ∩ f.symm ⁻¹' s) := f.isOpen_inter_preimage_symm s.2
  rw [← ofSet_trans _ openness₁, ← trans_assoc, ← trans_assoc]
  refine EqOnSource.trans' ?_ (eqOnSource_refl _)
  -- f' has been eliminated !!!
  have set_identity : f.symm.source ∩ (f.target ∩ f.symm ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s := by
    mfld_set_tac
  have openness₂ : IsOpen (s : Set X) := s.2
  rw [ofSet_trans', set_identity, ← trans_of_set' _ openness₂, trans_assoc]
  refine EqOnSource.trans' (eqOnSource_refl _) ?_
  -- f has been eliminated !!!
  refine Setoid.trans (symm_trans_self (s.openPartialHomeomorphSubtypeCoe hs)) ?_
  simp only [mfld_simps, Setoid.refl]
/-
**OpenPartialHomeomorph.subtypeRestr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OpenP
artialHomeomorph`。
形式化陈述：subtypeRestr_symm_apply {U : Opens X} (hU : Nonempty U) {y : Y} (hy : y in
 (e.subtypeRestr hU).target) : (Subtype.val ∘ (e.subtypeRestr hU).symm) y = e.sy
mm y
参数：hU : Nonempty U；hy : y in (e.subtypeRestr hU).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.eq_symm_apply`：eq_symm_apply {x : X} {y : Y} (hx :
 x in e.source) (hy : y in e.target) : x = e.symm y ↔ e x = y
· 使用定理 `OpenPartialHomeomorph.map_target`：map_target {x : Y} (h : x in e.target)
 : e.symm x in e.source
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_source`：subtypeRestr_source : (e.subt
ypeRestr hs).source = (↑) ⁻¹' e.source
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_coe`：subtypeRestr_coe : ((e.subtypeRe
str hs : OpenPartialHomeomorph s Y) : s -> Y) = Set.domRestrict ↑s (e : X -> Y)
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
-/
theorem subtypeRestr_symm_apply {U : Opens X} (hU : Nonempty U)
    {y : Y} (hy : y ∈ (e.subtypeRestr hU).target) :
    (Subtype.val ∘ (e.subtypeRestr hU).symm) y = e.symm y := by
  rw [e.eq_symm_apply _ hy.1]
  · change domRestrict _ e _ = _
    rw [← e.subtypeRestr_coe hU, (e.subtypeRestr hU).right_inv hy]
  · have := OpenPartialHomeomorph.map_target _ hy
    rwa [e.subtypeRestr_source] at this
/-
**OpenPartialHomeomorph.subtypeRestr_symm_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `OpenPa
rtialHomeomorph`。
形式化陈述：subtypeRestr_symm_eqOn {U : Opens X} (hU : Nonempty U) : EqOn e.symm (Subt
ype.val ∘ (e.subtypeRestr hU).symm) (e.subtypeRestr hU).target
参数：hU : Nonempty U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_symm_apply`：subtypeRestr_symm_apply {
U : Opens X} (hU : Nonempty U) {y : Y} (hy : y in (e.subtypeRestr hU).target) : 
(Subtype.val ∘ (e.subtypeRestr hU).…
-/
theorem subtypeRestr_symm_eqOn {U : Opens X} (hU : Nonempty U) :
    EqOn e.symm (Subtype.val ∘ (e.subtypeRestr hU).symm) (e.subtypeRestr hU).target :=
  fun _y hy ↦ (e.subtypeRestr_symm_apply hU hy).symm
/-
**OpenPartialHomeomorph.subtypeRestr_symm_eqOn_of_le** 是 Mathlib 中的一个定理，位于命名空间 `
OpenPartialHomeomorph`。
形式化陈述：subtypeRestr_symm_eqOn_of_le {U V : Opens X} (hU : Nonempty U) (hV : Nonem
pty V) (hUV : U <= V) : EqOn (e.subtypeRestr hV).symm (Set.inclusion hUV ∘ (e.su
btypeRestr hU).symm) (e.subtypeRestr hU).target
参数：hU : Nonempty U；hV : Nonempty V；hUV : U <= V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target`：openParti
alHomeomorphSubtypeCoe_target : (s.openPartialHomeomorphSubtypeCoe hs).target = 
s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `trivial`：True
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
-/
theorem subtypeRestr_symm_eqOn_of_le {U V : Opens X} (hU : Nonempty U) (hV : Nonempty V)
    (hUV : U ≤ V) : EqOn (e.subtypeRestr hV).symm (Set.inclusion hUV ∘ (e.subtypeRestr hU).symm)
      (e.subtypeRestr hU).target := by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [OpenPartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y ∈ (V.openPartialHomeomorphSubtypeCoe hV).target := by
    rw [Opens.openPartialHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine (V.openPartialHomeomorphSubtypeCoe hV).injOn ?_ trivial ?_
  · simp
  · rw [(V.openPartialHomeomorphSubtypeCoe hV).right_inv hyV]
    change _ = U.openPartialHomeomorphSubtypeCoe hU _
    rw [(U.openPartialHomeomorphSubtypeCoe hU).right_inv hy.2]

end subtypeRestr

/-!
## Extending along an open embedding
-/
section lift_openEmbedding

variable {X X' Z : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Z]
  [Nonempty Z] {f : X → X'}

/-- Extend an open partial homeomorphism `e : X → Z` to `X' → Z`, using an open embedding
`ι : X → X'`. On `ι(X)`, the extension is specified by `e`; its value elsewhere is arbitrary
(and uninteresting). -/
/-
**OpenPartialHomeomorph.lift_openEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartia
lHomeomorph`。
形式化陈述：lift_openEmbedding (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f
) : OpenPartialHomeomorph X' Z where toFun
参数：e : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
Extend an open partial homeomorphism `e : X → Z` to `X' → Z`, using an open embe
dding
`ι : X → X'`. On `ι(X)`, the extension is specified by `e`; its value elsewhere 
is arbitrary
(and uninteresting).
-/
noncomputable def lift_openEmbedding (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    OpenPartialHomeomorph X' Z where
  toFun := extend f e (fun _ ↦ (Classical.arbitrary Z))
  invFun := f ∘ e.invFun
  source := f '' e.source
  target := e.target
  map_source' := by
    rintro x ⟨x₀, hx₀, hxx₀⟩
    rw [← hxx₀, hf.injective.extend_apply e]
    exact e.map_source' hx₀
  map_target' z hz := mem_image_of_mem f (e.map_target' hz)
  left_inv' := by
    intro x ⟨x₀, hx₀, hxx₀⟩
    rw [← hxx₀, hf.injective.extend_apply e, comp_apply]
    congr
    exact e.left_inv' hx₀
  right_inv' z hz := by simpa only [comp_apply, hf.injective.extend_apply e] using! e.right_inv' hz
  open_source := hf.isOpenMap _ e.open_source
  open_target := e.open_target
  continuousOn_toFun := by
    by_cases Nonempty X; swap
    · intro x hx; simp_all
    set F := (extend f e (fun _ ↦ (Classical.arbitrary Z))) with F_eq
    have heq : EqOn F (e ∘ (hf.toOpenPartialHomeomorph).symm) (f '' e.source) := by
      intro x ⟨x₀, hx₀, hxx₀⟩
      rw [← hxx₀, F_eq, hf.injective.extend_apply e, comp_apply,
        hf.toOpenPartialHomeomorph_left_inv]
    have : ContinuousOn (e ∘ (hf.toOpenPartialHomeomorph).symm) (f '' e.source) := by
      apply e.continuousOn_toFun.comp; swap
      · intro x' ⟨x, hx, hx'x⟩
        rw [← hx'x, hf.toOpenPartialHomeomorph_left_inv]; exact hx
      have : ContinuousOn (hf.toOpenPartialHomeomorph).symm (f '' univ) :=
        (hf.toOpenPartialHomeomorph).continuousOn_invFun
      exact this.mono <| image_mono <| subset_univ _
    exact ContinuousOn.congr this heq
  continuousOn_invFun := hf.continuous.comp_continuousOn e.continuousOn_invFun

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.lift_openEmbedding_toFun** 是 Mathlib 中的一个引理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：lift_openEmbedding_toFun (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbed
ding f) : (e.lift_openEmbedding hf) = extend f e (fun _ => (Classical.arbitrary 
Z))
参数：e : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_openEmbedding_toFun (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf) = extend f e (fun _ ↦ (Classical.arbitrary Z)) := rfl
/-
**OpenPartialHomeomorph.lift_openEmbedding_apply** 是 Mathlib 中的一个引理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：lift_openEmbedding_apply (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbed
ding f) {x : X} : (lift_openEmbedding e hf) (f x) = e x
参数：e : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `OpenPartialHomeomorph.lift_openEmbedding_toFun`：lift_openEmbedding_toFun
 (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) : (e.lift_openEmbeddin
g hf) = extend f e (fun _ => (Classi…
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
-/
lemma lift_openEmbedding_apply (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) {x : X} :
    (lift_openEmbedding e hf) (f x) = e x := by
  simp_rw [e.lift_openEmbedding_toFun]
  apply hf.injective.extend_apply

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.lift_openEmbedding_source** 是 Mathlib 中的一个引理，位于命名空间 `Ope
nPartialHomeomorph`。
形式化陈述：lift_openEmbedding_source (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbe
dding f) : (e.lift_openEmbedding hf).source = f '' e.source
参数：e : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_openEmbedding_source (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).source = f '' e.source := rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.lift_openEmbedding_target** 是 Mathlib 中的一个引理，位于命名空间 `Ope
nPartialHomeomorph`。
形式化陈述：lift_openEmbedding_target (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbe
dding f) : (e.lift_openEmbedding hf).target = e.target
参数：e : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_openEmbedding_target (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).target = e.target := rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.lift_openEmbedding_symm** 是 Mathlib 中的一个引理，位于命名空间 `OpenP
artialHomeomorph`。
形式化陈述：lift_openEmbedding_symm (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedd
ing f) : (e.lift_openEmbedding hf).symm = f ∘ e.symm
参数：e : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_openEmbedding_symm (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm = f ∘ e.symm := rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.lift_openEmbedding_symm_source** 是 Mathlib 中的一个引理，位于命名空间
 `OpenPartialHomeomorph`。
形式化陈述：lift_openEmbedding_symm_source (e : OpenPartialHomeomorph X Z) (hf : IsOpe
nEmbedding f) : (e.lift_openEmbedding hf).symm.source = e.target
参数：e : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_openEmbedding_symm_source (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.source = e.target := rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.lift_openEmbedding_symm_target** 是 Mathlib 中的一个引理，位于命名空间
 `OpenPartialHomeomorph`。
形式化陈述：lift_openEmbedding_symm_target (e : OpenPartialHomeomorph X Z) (hf : IsOpe
nEmbedding f) : (e.lift_openEmbedding hf).symm.target = f '' e.source
参数：e : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.symm_target`：symm_target : e.symm.target = e.sourc
e
· 使用引理 `OpenPartialHomeomorph.lift_openEmbedding_source`：lift_openEmbedding_sour
ce (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) : (e.lift_openEmbedd
ing hf).source = f '' e.source
-/
lemma lift_openEmbedding_symm_target (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.target = f '' e.source := by
  rw [OpenPartialHomeomorph.symm_target, e.lift_openEmbedding_source]
/-
**OpenPartialHomeomorph.lift_openEmbedding_trans_apply** 是 Mathlib 中的一个引理，位于命名空间
 `OpenPartialHomeomorph`。
形式化陈述：lift_openEmbedding_trans_apply (e e' : OpenPartialHomeomorph X Z) (hf : Is
OpenEmbedding f) (z : Z) : (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmb
edding hf) z = (e.symm.trans e') z
参数：e e' : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f；z : Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_openEmbedding_trans_apply
    (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) (z : Z) :
    (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmbedding hf) z = (e.symm.trans e') z := by
  simp [hf.injective.extend_apply e']

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.lift_openEmbedding_trans** 是 Mathlib 中的一个引理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：lift_openEmbedding_trans (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEm
bedding f) : (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmbedding hf) = e
.symm.trans e'
参数：e e' : OpenPartialHomeomorph X Z；hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.ext`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y]   (e e' : OpenPartialHomeomorph X Y
),   (∀ (x : X)…
· 使用引理 `OpenPartialHomeomorph.lift_openEmbedding_trans_apply`：lift_openEmbedding
_trans_apply (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) (z : Z)
 : (e.lift_openEmbedding hf).symm.trans (e…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.trans_source`：trans_source : (e.trans e').source =
 e.source inter e ⁻¹' e'.source
· 使用引理 `OpenPartialHomeomorph.lift_openEmbedding_symm_source`：lift_openEmbedding
_symm_source (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) : (e.lift_
openEmbedding hf).symm.source = e.target
· 使用引理 `OpenPartialHomeomorph.lift_openEmbedding_symm`：lift_openEmbedding_symm (
e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) : (e.lift_openEmbedding 
hf).symm = f ∘ e.symm
· 使用引理 `OpenPartialHomeomorph.lift_openEmbedding_source`：lift_openEmbedding_sour
ce (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) : (e.lift_openEmbedd
ing hf).source = f '' e.source
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma lift_openEmbedding_trans (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmbedding hf) = e.symm.trans e' := by
  ext z
  · exact e.lift_openEmbedding_trans_apply e' hf z
  · simp [hf.injective.extend_apply e]
  · simp_rw [OpenPartialHomeomorph.trans_source, e.lift_openEmbedding_symm_source, e.symm_source,
      e.lift_openEmbedding_symm, e'.lift_openEmbedding_source]
    refine ⟨fun ⟨hx, ⟨y, hy, hxy⟩⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, hx'⟩ ↦ ⟨hx, mem_image_of_mem f hx'⟩⟩
    rw [mem_preimage]; rw [comp_apply] at hxy
    exact (hf.injective hxy) ▸ hy

end lift_openEmbedding

end OpenPartialHomeomorph

