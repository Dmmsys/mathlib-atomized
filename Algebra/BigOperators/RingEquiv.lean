/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Results about mapping big operators across ring equivalences
-/

public section


namespace RingEquiv

variable {α R S : Type*}

/-
**RingEquiv.map_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] 
(f : R ≃+* S) (l : List R),   f l.prod = (List.map (⇑f) l).prod
参数：f : R ≃+* S；l : List R；List.map (⇑f) l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_list_prod [Semiring R] [Semiring S] (f : R ≃+* S) (l : List R) :
    f l.prod = (l.map f).prod := map_list_prod f l
/-
**RingEquiv.map_list_sum** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_2} {S : Type u_3} [inst : NonUnitalNonAssocSemiring R] [inst
_1 : NonUnitalNonAssocSemiring S]   (f : R ≃+* S) (l : List R), f l.sum = (List.
map (⇑f) l).sum
参数：f : R ≃+* S；l : List R；List.map (⇑f) l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_list_sum [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R ≃+* S) (l : List R) : f l.sum = (l.map f).sum := map_list_sum f l

/-- An isomorphism into the opposite ring acts on the product by acting on the reversed elements -/
/-
**RingEquiv.unop_map_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] 
(f : R ≃+* Sᵐᵒᵖ) (l : List R),   MulOpposite.unop (f l.prod) = (List.map (MulOpp
osite.unop ∘ ⇑f) l).reverse.prod
参数：f : R ≃+* Sᵐᵒᵖ；l : List R；f l.prod；List.map (MulOpposite.unop ∘ ⇑f) l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `unop_map_list_prod`：unop_map_list_prod {F : Type*} [FunLike F M Nᵐᵒᵖ] [M
onoidHomClass F M Nᵐᵒᵖ] (f : F) (l : List M) : (f l.prod).unop = (l.map (MulOppo
site.uno…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
An isomorphism into the opposite ring acts on the product by acting on the rever
sed elements
-/
protected theorem unop_map_list_prod [Semiring R] [Semiring S] (f : R ≃+* Sᵐᵒᵖ) (l : List R) :
    MulOpposite.unop (f l.prod) = (l.map (MulOpposite.unop ∘ f)).reverse.prod :=
  unop_map_list_prod f l
/-
**RingEquiv.map_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_2} {S : Type u_3} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] (f : R ≃+* S) (s : Multiset R),   f s.prod = (Multiset.map (⇑f) s).prod
参数：f : R ≃+* S；s : Multiset R；Multiset.map (⇑f) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_multiset_prod [CommSemiring R] [CommSemiring S] (f : R ≃+* S)
    (s : Multiset R) : f s.prod = (s.map f).prod :=
  map_multiset_prod f s
/-
**RingEquiv.map_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_2} {S : Type u_3} [inst : NonUnitalNonAssocSemiring R] [inst
_1 : NonUnitalNonAssocSemiring S]   (f : R ≃+* S) (s : Multiset R), f s.sum = (M
ultiset.map (⇑f) s).sum
参数：f : R ≃+* S；s : Multiset R；Multiset.map (⇑f) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_multiset_sum [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R ≃+* S) (s : Multiset R) : f s.sum = (s.map f).sum :=
  map_multiset_sum f s
/-
**RingEquiv.map_prod** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {S : Type u_3} [inst : CommSemiring R] [in
st_1 : CommSemiring S] (g : R ≃+* S)   (f : α → R) (s : Finset α), g (∏ x ∈ s, f
 x) = ∏ x ∈ s, g (f x)
参数：g : R ≃+* S；f : α → R；s : Finset α；∏ x ∈ s, f x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_prod [CommSemiring R] [CommSemiring S] (g : R ≃+* S) (f : α → R)
    (s : Finset α) : g (∏ x ∈ s, f x) = ∏ x ∈ s, g (f x) :=
  map_prod g f s
/-
**RingEquiv.map_sum** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {S : Type u_3} [inst : NonUnitalNonAssocSe
miring R]   [inst_1 : NonUnitalNonAssocSemiring S] (g : R ≃+* S) (f : α → R) (s 
: Finset α), g (∑ x ∈ s, f x) = ∑ x ∈ s, g (f x)
参数：g : R ≃+* S；f : α → R；s : Finset α；∑ x ∈ s, f x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_sum [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (g : R ≃+* S)
    (f : α → R) (s : Finset α) : g (∑ x ∈ s, f x) = ∑ x ∈ s, g (f x) :=
  map_sum g f s

end RingEquiv

