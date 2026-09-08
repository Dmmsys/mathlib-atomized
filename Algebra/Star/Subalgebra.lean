/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# Star subalgebras

A \*-subalgebra is a subalgebra of a \*-algebra which is closed under `*`.

The centralizer of a \*-closed set is a \*-subalgebra.
-/

@[expose] public section

universe u v

/-- A \*-subalgebra is a subalgebra of a \*-algebra which is closed under `*`. -/
/-
**StarSubalgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (A : Type v) →     [inst : CommSemiring R] →       [inst_
1 : StarRing R] →         [inst_2 : Semiring A] → [inst_3 : StarRing A] → [inst_
4 : Algebra R A] → [StarModule R A] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A \*-subalgebra is a subalgebra of a \*-algebra which is closed under `*`.
-/
structure StarSubalgebra (R : Type u) (A : Type v) [CommSemiring R] [StarRing R] [Semiring A]
    [StarRing A] [Algebra R A] [StarModule R A] : Type v extends Subalgebra R A where
  /-- The `carrier` is closed under the `star` operation. -/
  star_mem' {a} : a ∈ carrier → star a ∈ carrier

namespace StarSubalgebra

/-- Forgetting that a \*-subalgebra is closed under \*.
-/
add_decl_doc StarSubalgebra.toSubalgebra

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]
variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]
variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

/-
**StarSubalgebra.setLike** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：setLike : SetLike (StarSubalgebra R A) A where coe S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance setLike : SetLike (StarSubalgebra R A) A where
  coe S := S.carrier
  coe_injective p q h := by obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr
/-
**StarSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (StarSubalgebra R A) := .ofSetLike (StarSubalgebra R A) A

/-- The actual `StarSubalgebra` obtained from an element of a type satisfying `SubsemiringClass`,
`SMulMemClass` and `StarMemClass`. -/
@[simps]
/-
**StarSubalgebra.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `StarSubalgebra`。
形式化陈述：ofClass {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [StarR
ing R] [StarRing A] [StarModule R A] [SetLike S A] [SubsemiringClass S A] [SMulM
emClass S R A] [StarMemClass S A] (s : S) : StarSubalgebra R A where carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `StarSubalgebra` obtained from an element of a type satisfying `Subse
miringClass`,
`SMulMemClass` and `StarMemClass`.
-/
def ofClass {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [StarRing R] [StarRing A]
    [StarModule R A] [SetLike S A] [SubsemiringClass S A] [SMulMemClass S R A] [StarMemClass S A]
    (s : S) : StarSubalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' := algebraMap_mem s
  star_mem' := star_mem
/-
**StarSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set A) (StarSubalgebra R A) (↑)
    (fun s ↦ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧
      (∀ (r : R), algebraMap R A r ∈ s) ∧ ∀ {x}, x ∈ s → star x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := by simpa using h.2.2.1 0
        add_mem' := h.1
        one_mem' := by simpa using h.2.2.1 1
        mul_mem' := h.2.1
        algebraMap_mem' := h.2.2.1
        star_mem' := h.2.2.2 },
      rfl ⟩
/-
**StarSubalgebra.starMemClass** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：starMemClass : StarMemClass (StarSubalgebra R A) A where star_mem {s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.star_mem'`：∀ {R : Type u} {A : Type v} [inst : CommSemiri
ng R] [inst_1 : StarRing R] [inst_2 : Semiring A] [inst_3 : StarRing A]   [inst_
4 : Algebra R …
-/
instance starMemClass : StarMemClass (StarSubalgebra R A) A where
  star_mem {s} := s.star_mem'
/-
**StarSubalgebra.subsemiringClass** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：subsemiringClass : SubsemiringClass (StarSubalgebra R A) A where add_mem {
s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mul_mem'`：∀ {M : Type u_3} [inst : Mul M] (self : Subsemigr
oup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier
· 使用定理 `Submonoid.one_mem'`：∀ {M : Type u_3} [inst : MulOneClass M] (self : Subm
onoid M), 1 ∈ self.carrier
· 使用定理 `Subsemiring.add_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self :
 Subsemiring R) {a b : R},   a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.
carrier
· 使用定理 `Subsemiring.zero_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self 
: Subsemiring R), 0 ∈ self.carrier
-/
instance subsemiringClass : SubsemiringClass (StarSubalgebra R A) A where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'
/-
**StarSubalgebra.smulMemClass** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：smulMemClass : SMulMemClass (StarSubalgebra R A) R A where smul_mem {s} r 
a (ha : a in s.toSubalgebra)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
-/
instance smulMemClass : SMulMemClass (StarSubalgebra R A) R A where
  smul_mem {s} r a (ha : a ∈ s.toSubalgebra) :=
    (SMulMemClass.smul_mem r ha : r • a ∈ s.toSubalgebra)
/-
**StarSubalgebra.subringClass** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：subringClass {R A} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebr
a R A] [StarModule R A] : SubringClass (StarSubalgebra R A) A where neg_mem {s a
} ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
instance subringClass {R A} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
    [StarModule R A] : SubringClass (StarSubalgebra R A) A where
  neg_mem {s a} ha := show -a ∈ s.toSubalgebra from neg_mem ha

-- this uses the `Star` instance `s` inherits from `StarMemClass (StarSubalgebra R A) A`
/-
**StarSubalgebra.starRing** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：starRing (s : StarSubalgebra R A) : StarRing s
参数：s : StarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance starRing (s : StarSubalgebra R A) : StarRing s :=
  { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : A))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : A) (r₂ : A))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : A) (r₂ : A)) }
/-
**StarSubalgebra.algebra** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：algebra (s : StarSubalgebra R A) : Algebra R s
参数：s : StarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra (s : StarSubalgebra R A) : Algebra R s :=
  s.toSubalgebra.algebra'
/-
**StarSubalgebra.starModule** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：starModule (s : StarSubalgebra R A) : StarModule R s where star_smul r a
参数：s : StarSubalgebra R A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
-/
instance starModule (s : StarSubalgebra R A) : StarModule R s where
  star_smul r a := Subtype.ext (star_smul r (a : A))

/-- Turn a `StarSubalgebra` into a `NonUnitalStarSubalgebra` by forgetting that it contains `1`. -/
@[reducible]
/-
**StarSubalgebra.toNonUnitalStarSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `StarSubalg
ebra`。
形式化陈述：toNonUnitalStarSubalgebra (S : StarSubalgebra R A) : NonUnitalStarSubalgeb
ra R A where __
参数：S : StarSubalgebra R A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.star_mem'`：∀ {R : Type u} {A : Type v} [inst : CommSemiri
ng R] [inst_1 : StarRing R] [inst_2 : Semiring A] [inst_3 : StarRing A]   [inst_
4 : Algebra R …

--- 原说明 ---
Turn a `StarSubalgebra` into a `NonUnitalStarSubalgebra` by forgetting that it c
ontains `1`.
-/
def toNonUnitalStarSubalgebra (S : StarSubalgebra R A) : NonUnitalStarSubalgebra R A where
  __ := S
  smul_mem' r _x hx := S.smul_mem hx r
/-
**StarSubalgebra.one_mem_toNonUnitalStarSubalgebra** 是 Mathlib 中的一个引理，位于命名空间 `St
arSubalgebra`。
形式化陈述：one_mem_toNonUnitalStarSubalgebra (S : StarSubalgebra R A) : 1 in S.toNonU
nitalStarSubalgebra
参数：S : StarSubalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.one_mem'`：∀ {M : Type u_3} [inst : MulOneClass M] (self : Subm
onoid M), 1 ∈ self.carrier
-/
lemma one_mem_toNonUnitalStarSubalgebra (S : StarSubalgebra R A) :
    1 ∈ S.toNonUnitalStarSubalgebra := S.one_mem'

@[simp]
/-
**StarSubalgebra.mem_toNonUnitalStarSubalgebra** 是 Mathlib 中的一个引理，位于命名空间 `StarSu
balgebra`。
形式化陈述：mem_toNonUnitalStarSubalgebra {S : StarSubalgebra R A} {x : A} : x in S.to
NonUnitalStarSubalgebra ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_toNonUnitalStarSubalgebra {S : StarSubalgebra R A} {x : A} :
    x ∈ S.toNonUnitalStarSubalgebra ↔ x ∈ S :=
  Iff.rfl
/-
**StarSubalgebra.toNonUnitalStarSubalgebra_injective** 是 Mathlib 中的一个引理，位于命名空间 `
StarSubalgebra`。
形式化陈述：toNonUnitalStarSubalgebra_injective : Function.Injective (toNonUnitalStarS
ubalgebra : StarSubalgebra R A -> NonUnitalStarSubalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma toNonUnitalStarSubalgebra_injective : Function.Injective
    (toNonUnitalStarSubalgebra : StarSubalgebra R A → NonUnitalStarSubalgebra R A) :=
  fun _ _ ↦ by simp [SetLike.ext_iff]
/-
**StarSubalgebra.toNonUnitalStarSubalgebra_inj** 是 Mathlib 中的一个引理，位于命名空间 `StarSu
balgebra`。
形式化陈述：toNonUnitalStarSubalgebra_inj {S U : StarSubalgebra R A} : S.toNonUnitalSt
arSubalgebra = U.toNonUnitalStarSubalgebra ↔ S = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `StarSubalgebra.toNonUnitalStarSubalgebra_injective`：toNonUnitalStarSubal
gebra_injective : Function.Injective (toNonUnitalStarSubalgebra : StarSubalgebra
 R A -> NonUnitalStarSubalgebra R A)
-/
lemma toNonUnitalStarSubalgebra_inj {S U : StarSubalgebra R A} :
    S.toNonUnitalStarSubalgebra = U.toNonUnitalStarSubalgebra ↔ S = U :=
  toNonUnitalStarSubalgebra_injective.eq_iff
/-
**StarSubalgebra.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_carrier {s : StarSubalgebra R A} {x : A} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : StarSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
/-
**StarSubalgebra.ext** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：ext {S T : StarSubalgebra R A} (h : forall x : A, x in S ↔ x in T) : S = T
参数：h : forall x : A, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {S T : StarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
/-
**StarSubalgebra.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_mk (S : Subalgebra R A) (h) : ((⟨S, h⟩ : StarSubalgebra R A) : Set A) 
= S
参数：S : Subalgebra R A；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk (S : Subalgebra R A) (h) : ((⟨S, h⟩ : StarSubalgebra R A) : Set A) = S := rfl

@[simp]
/-
**StarSubalgebra.mem_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_toSubalgebra {S : StarSubalgebra R A} {x} : x in S.toSubalgebra ↔ x in
 S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubalgebra {S : StarSubalgebra R A} {x} : x ∈ S.toSubalgebra ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**StarSubalgebra.coe_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_toSubalgebra (S : StarSubalgebra R A) : (S.toSubalgebra : Set A) = S
参数：S : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubalgebra (S : StarSubalgebra R A) : (S.toSubalgebra : Set A) = S :=
  rfl
/-
**StarSubalgebra.toSubalgebra_injective** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebr
a`。
形式化陈述：toSubalgebra_injective : Function.Injective (toSubalgebra : StarSubalgebra
 R A -> Subalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.ext`：ext {S T : StarSubalgebra R A} (h : forall x : A, x 
in S ↔ x in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StarSubalgebra.mem_toSubalgebra`：mem_toSubalgebra {S : StarSubalgebra R 
A} {x} : x in S.toSubalgebra ↔ x in S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubalgebra_injective :
    Function.Injective (toSubalgebra : StarSubalgebra R A → Subalgebra R A) := fun S T h =>
  ext fun x => by rw [← mem_toSubalgebra, ← mem_toSubalgebra, h]
/-
**StarSubalgebra.toSubalgebra_inj** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：toSubalgebra_inj {S U : StarSubalgebra R A} : S.toSubalgebra = U.toSubalge
bra ↔ S = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StarSubalgebra.toSubalgebra_injective`：toSubalgebra_injective : Function
.Injective (toSubalgebra : StarSubalgebra R A -> Subalgebra R A)
-/
theorem toSubalgebra_inj {S U : StarSubalgebra R A} : S.toSubalgebra = U.toSubalgebra ↔ S = U :=
  toSubalgebra_injective.eq_iff
/-
**StarSubalgebra.toSubalgebra_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：toSubalgebra_le_iff {S₁ S₂ : StarSubalgebra R A} : S₁.toSubalgebra <= S₂.t
oSubalgebra ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubalgebra_le_iff {S₁ S₂ : StarSubalgebra R A} :
    S₁.toSubalgebra ≤ S₂.toSubalgebra ↔ S₁ ≤ S₂ :=
  Iff.rfl

/-- Copy of a star subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
/-
**StarSubalgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 `StarSubalgebra`。
形式化陈述：{R : Type u_2} →   {A : Type u_3} →     [inst : CommSemiring R] →       [i
nst_1 : StarRing R] →         [inst_2 : Semiring A] →           [inst_3 : StarRi
ng A] →             [inst_4 : Algebra R A] →               [inst_5 : StarModule 
R A] → (S : StarSubalgebra R A) → (s : Set A) → s = ↑S → StarSubalgebra R A
参数：S : StarSubalgebra R A；s : Set A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a star subalgebra with a new `carrier` equal to the old one. Useful to f
ix definitional
equalities.
-/
protected def copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.copy S.toSubalgebra s hs
  star_mem' {a} ha := hs ▸ S.star_mem' (by simpa [hs] using ha)

@[simp, norm_cast]
/-
**StarSubalgebra.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs
 : Set A) = s
参数：S : StarSubalgebra R A；s : Set A；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs : Set A) = s :=
  rfl
/-
**StarSubalgebra.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：copy_eq (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs =
 S
参数：S : StarSubalgebra R A；s : Set A；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : StarSubalgebra R A)
/-
**StarSubalgebra.algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemiring R] [inst_1 : StarRing
 R] [inst_2 : Semiring A]   [inst_3 : StarRing A] [inst_4 : Algebra R A] [inst_5
 : StarModule R A] (S : StarSubalgebra R A) (r : R),   (algebraMap R A) r ∈ S
参数：S : StarSubalgebra R A；r : R；algebraMap R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.algebraMap_mem'`：∀ {R : Type u} {A : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (self : Subalgebra R A)   (
r : R), (algebra…
-/
protected theorem algebraMap_mem (r : R) : algebraMap R A r ∈ S :=
  S.algebraMap_mem' r
/-
**StarSubalgebra.rangeS_le** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：rangeS_le : (algebraMap R A).rangeS <= S.toSubalgebra.toSubsemiring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.algebraMap_mem`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : StarRing R] [inst_2 : Semiring A]   [inst_3 : StarRing 
A] [inst_4 : Algebr…
-/
theorem rangeS_le : (algebraMap R A).rangeS ≤ S.toSubalgebra.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r
/-
**StarSubalgebra.range_subset** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：range_subset : Set.range (algebraMap R A) subseteq S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.algebraMap_mem`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : StarRing R] [inst_2 : Semiring A]   [inst_3 : StarRing 
A] [inst_4 : Algebr…
-/
theorem range_subset : Set.range (algebraMap R A) ⊆ S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r
/-
**StarSubalgebra.range_le** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：range_le : Set.range (algebraMap R A) <= S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.range_subset`：range_subset : Set.range (algebraMap R A) s
ubseteq S
-/
theorem range_le : Set.range (algebraMap R A) ≤ S :=
  S.range_subset
/-
**StarSubalgebra.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemiring R] [inst_1 : StarRing
 R] [inst_2 : Semiring A]   [inst_3 : StarRing A] [inst_4 : Algebra R A] [inst_5
 : StarModule R A] (S : StarSubalgebra R A) {x : A},   x ∈ S → ∀ (r : R), r • x 
∈ S
参数：S : StarSubalgebra R A；r : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `StarSubalgebra.algebraMap_mem`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : StarRing R] [inst_2 : Semiring A]   [inst_3 : StarRing 
A] [inst_4 : Algebr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
protected theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem r) hx

/-- Embedding of a subalgebra into the algebra. -/
/-
**StarSubalgebra.subtype** 是 Mathlib 中的一个定义，位于命名空间 `StarSubalgebra`。
形式化陈述：subtype : S ->⋆ₐ[R] A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of a subalgebra into the algebra.
-/
def subtype : S →⋆ₐ[R] A where
  toFun := ((↑) : S → A)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
/-
**StarSubalgebra.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_subtype : (S.subtype : S -> A) = Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : (S.subtype : S → A) = Subtype.val :=
  rfl
/-
**StarSubalgebra.subtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：subtype_apply (x : S) : S.subtype x = (x : A)
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply (x : S) : S.subtype x = (x : A) :=
  rfl

@[simp]
/-
**StarSubalgebra.toSubalgebra_subtype** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`
。
形式化陈述：toSubalgebra_subtype : S.toSubalgebra.val = S.subtype.toAlgHom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubalgebra_subtype : S.toSubalgebra.val = S.subtype.toAlgHom :=
  rfl

/-- The inclusion map between `StarSubalgebra`s given by `Subtype.map id` as a `StarAlgHom`. -/
@[simps]
/-
**StarSubalgebra.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `StarSubalgebra`。
形式化陈述：inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂) : S₁ ->⋆ₐ[R] S₂ wher
e toFun
参数：h : S₁ <= S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map between `StarSubalgebra`s given by `Subtype.map id` as a `Star
AlgHom`.
-/
def inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) : S₁ →⋆ₐ[R] S₂ where
  toFun := Subtype.map id h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
/-
**StarSubalgebra.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：inclusion_injective {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂) : Function
.Injective inclusion h
参数：h : S₁ <= S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem inclusion_injective {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    Function.Injective <| inclusion h :=
  Set.inclusion_injective h

@[simp]
/-
**StarSubalgebra.subtype_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebr
a`。
形式化陈述：subtype_comp_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂) : S₂.su
btype.comp (inclusion h) = S₁.subtype
参数：h : S₁ <= S₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_comp_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    S₂.subtype.comp (inclusion h) = S₁.subtype :=
  rfl

section Map

/-- Transport a star subalgebra via a star algebra homomorphism. -/
/-
**StarSubalgebra.map** 是 Mathlib 中的一个定义，位于命名空间 `StarSubalgebra`。
形式化陈述：map (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R A) : StarSubalgebra R B
参数：f : A ->⋆ₐ[R] B；S : StarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a star subalgebra via a star algebra homomorphism.
-/
def map (f : A →⋆ₐ[R] B) (S : StarSubalgebra R A) : StarSubalgebra R B :=
  { S.toSubalgebra.map f.toAlgHom with
    star_mem' := by
      rintro _ ⟨a, ha, rfl⟩
      exact map_star f a ▸ Set.mem_image_of_mem _ (S.star_mem' ha) }
/-
**StarSubalgebra.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：map_mono {S₁ S₂ : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} : S₁ <= S₂ -> S₁.m
ap f <= S₂.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono {S₁ S₂ : StarSubalgebra R A} {f : A →⋆ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_mono
/-
**StarSubalgebra.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：map_injective {f : A ->⋆ₐ[R] B} (hf : Function.Injective f) : Function.Inj
ective (map f)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.ext`：ext {S T : StarSubalgebra R A} (h : forall x : A, x 
in S ↔ x in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem map_injective {f : A →⋆ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
/-
**StarSubalgebra.map_id** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：map_id (S : StarSubalgebra R A) : S.map (StarAlgHom.id R A) = S
参数：S : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (S : StarSubalgebra R A) : S.map (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _
/-
**StarSubalgebra.map_map** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：map_map (S : StarSubalgebra R A) (g : B ->⋆ₐ[R] C) (f : A ->⋆ₐ[R] B) : (S.
map f).map g = S.map (g.comp f)
参数：S : StarSubalgebra R A；g : B ->⋆ₐ[R] C；f : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (S : StarSubalgebra R A) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

@[simp]
/-
**StarSubalgebra.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_map {S : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} {y : B} : y in map f S 
↔ exists x in S, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subsemiring.mem_map`：mem_map {f : R ->+* S} {s : Subsemiring R} {y : S} 
: y in s.map f ↔ exists x in s, f x = y
-/
theorem mem_map {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {y : B} :
    y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  Subsemiring.mem_map
/-
**StarSubalgebra.map_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：map_toSubalgebra {S : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} : (S.map f).to
Subalgebra = S.toSubalgebra.map f.toAlgHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem map_toSubalgebra {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} :
    (S.map f).toSubalgebra = S.toSubalgebra.map f.toAlgHom :=
  SetLike.coe_injective rfl

@[simp, norm_cast]
/-
**StarSubalgebra.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_map (S : StarSubalgebra R A) (f : A ->⋆ₐ[R] B) : (S.map f : Set B) = f
 '' S
参数：S : StarSubalgebra R A；f : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (S : StarSubalgebra R A) (f : A →⋆ₐ[R] B) : (S.map f : Set B) = f '' S :=
  rfl

/-- Preimage of a star subalgebra under a star algebra homomorphism. -/
/-
**StarSubalgebra.comap** 是 Mathlib 中的一个定义，位于命名空间 `StarSubalgebra`。
形式化陈述：comap (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) : StarSubalgebra R A
参数：f : A ->⋆ₐ[R] B；S : StarSubalgebra R B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preimage of a star subalgebra under a star algebra homomorphism.
-/
def comap (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) : StarSubalgebra R A :=
  { S.toSubalgebra.comap f.toAlgHom with
    star_mem' := @fun a ha => show f (star a) ∈ S from (map_star f a).symm ▸ star_mem ha }
/-
**StarSubalgebra.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：map_le_iff_le_comap {S : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} {U : StarSu
balgebra R B} : map f S <= U ↔ S <= comap f U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {U : StarSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff
/-
**StarSubalgebra.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：gc_map_comap (f : A ->⋆ₐ[R] B) : GaloisConnection (map f) (comap f)
参数：f : A ->⋆ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.map_le_iff_le_comap`：map_le_iff_le_comap {S : StarSubalge
bra R A} {f : A ->⋆ₐ[R] B} {U : StarSubalgebra R B} : map f S <= U ↔ S <= comap 
f U
-/
theorem gc_map_comap (f : A →⋆ₐ[R] B) : GaloisConnection (map f) (comap f) := fun _S _U =>
  map_le_iff_le_comap

@[gcongr]
/-
**StarSubalgebra.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：comap_mono {S₁ S₂ : StarSubalgebra R B} {f : A ->⋆ₐ[R] B} : S₁ <= S₂ -> S₁
.comap f <= S₂.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem comap_mono {S₁ S₂ : StarSubalgebra R B} {f : A →⋆ₐ[R] B} :
    S₁ ≤ S₂ → S₁.comap f ≤ S₂.comap f :=
  Set.preimage_mono
/-
**StarSubalgebra.comap_injective** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：comap_injective {f : A ->⋆ₐ[R] B} (hf : Function.Surjective f) : Function.
Injective (comap f)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.ext`：ext {S T : StarSubalgebra R A} (h : forall x : A, x 
in S ↔ x in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem comap_injective {f : A →⋆ₐ[R] B} (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun _S₁ _S₂ h =>
  ext fun b =>
    let ⟨x, hx⟩ := hf b
    let := SetLike.ext_iff.1 h x
    hx ▸ this

@[simp]
/-
**StarSubalgebra.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：comap_id (S : StarSubalgebra R A) : S.comap (StarAlgHom.id R A) = S
参数：S : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_id`：preimage_id {s : Set α} : id ⁻¹' s = s
-/
theorem comap_id (S : StarSubalgebra R A) : S.comap (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.preimage_id
/-
**StarSubalgebra.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：comap_comap (S : StarSubalgebra R C) (g : B ->⋆ₐ[R] C) (f : A ->⋆ₐ[R] B) :
 (S.comap g).comap f = S.comap (g.comp f)
参数：S : StarSubalgebra R C；g : B ->⋆ₐ[R] C；f : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
-/
theorem comap_comap (S : StarSubalgebra R C) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  SetLike.coe_injective <| by exact Set.preimage_preimage

@[simp]
/-
**StarSubalgebra.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_comap (S : StarSubalgebra R B) (f : A ->⋆ₐ[R] B) (x : A) : x in S.coma
p f ↔ f x in S
参数：S : StarSubalgebra R B；f : A ->⋆ₐ[R] B；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
/-
**StarSubalgebra.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_comap (S : StarSubalgebra R B) (f : A ->⋆ₐ[R] B) : (S.comap f : Set A)
 = f ⁻¹' (S : Set B)
参数：S : StarSubalgebra R B；f : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) :
    (S.comap f : Set A) = f ⁻¹' (S : Set B) :=
  rfl

end Map

section Centralizer

variable (R)

/-- The centralizer, or commutant, of the star-closure of a set as a star subalgebra. -/
/-
**StarSubalgebra.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `StarSubalgebra`。
形式化陈述：centralizer (s : Set A) : StarSubalgebra R A where toSubalgebra
参数：s : Set A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centralizer, or commutant, of the star-closure of a set as a star subalgebra
.
-/
def centralizer (s : Set A) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.centralizer R (s ∪ star s)
  star_mem' := Set.star_mem_centralizer

@[simp, norm_cast]
/-
**StarSubalgebra.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s union star s)
.centralizer
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s ∪ star s).centralizer :=
  rfl

open Set in
nonrec theorem mem_centralizer_iff {s : Set A} {z : A} :
    z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g := by
  simp [← SetLike.mem_coe, centralizer_union, ← image_star, mem_centralizer_iff, forall_and]
/-
**StarSubalgebra.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：centralizer_le (s t : Set A) (h : s subseteq t) : centralizer R t <= centr
alizer R s
参数：s t : Set A；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.centralizer_subset`：centralizer_subset (h : S subseteq T) : centrali
zer T subseteq centralizer S
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)
/-
**StarSubalgebra.centralizer_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalge
bra`。
形式化陈述：centralizer_toSubalgebra (s : Set A) : (centralizer R s).toSubalgebra = Su
balgebra.centralizer R (s union star s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_toSubalgebra (s : Set A) :
    (centralizer R s).toSubalgebra = Subalgebra.centralizer R (s ∪ star s) :=
  rfl
/-
**StarSubalgebra.coe_centralizer_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `StarSuba
lgebra`。
形式化陈述：coe_centralizer_centralizer (s : Set A) : (centralizer R (centralizer R s 
: Set A)) = (s union star s).centralizer.centralizer
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.coe_centralizer`：coe_centralizer (s : Set A) : (centraliz
er R s : Set A) = (s union star s).centralizer
· 使用引理 `StarMemClass.star_coe_eq`：StarMemClass.star_coe_eq {S α : Type*} [Involu
tiveStar α] [SetLike S α] [StarMemClass S α] (s : S) : star (s : Set α) = s
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
-/
theorem coe_centralizer_centralizer (s : Set A) :
    (centralizer R (centralizer R s : Set A)) = (s ∪ star s).centralizer.centralizer := by
  rw [coe_centralizer, StarMemClass.star_coe_eq, Set.union_self, coe_centralizer]

end Centralizer

end StarSubalgebra

/-! ### The star closure of a subalgebra -/
namespace Subalgebra

open scoped Pointwise

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- The pointwise `star` of a subalgebra is a subalgebra. -/
/-
**Subalgebra.involutiveStar** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：involutiveStar : InvolutiveStar (Subalgebra R A) where star S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pointwise `star` of a subalgebra is a subalgebra.
-/
instance involutiveStar : InvolutiveStar (Subalgebra R A) where
  star S :=
    { carrier := star S.carrier
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_mul x y).symm ▸ mul_mem hy hx
      one_mem' := Set.mem_star.mp ((star_one A).symm ▸ one_mem S : star (1 : A) ∈ S)
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_add x y).symm ▸ add_mem hx hy
      zero_mem' := Set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) ∈ S)
      algebraMap_mem' := fun r => by
        simpa only [Set.mem_star, Subalgebra.mem_carrier, ← algebraMap_star_comm] using
          S.algebraMap_mem (star r) }
  star_involutive S :=
    Subalgebra.ext fun x =>
      ⟨fun hx => star_star x ▸ hx, fun hx => ((star_star x).symm ▸ hx : star (star x) ∈ S)⟩

@[simp]
/-
**Subalgebra.mem_star_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_star_iff (S : Subalgebra R A) (x : A) : x in star S ↔ star x in S
参数：S : Subalgebra R A；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_star_iff (S : Subalgebra R A) (x : A) : x ∈ star S ↔ star x ∈ S :=
  Iff.rfl
/-
**Subalgebra.star_mem_star_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：star_mem_star_iff (S : Subalgebra R A) (x : A) : star x in star S ↔ x in S
参数：S : Subalgebra R A；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem star_mem_star_iff (S : Subalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S := by
  simp

@[simp]
/-
**Subalgebra.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_star (S : Subalgebra R A) : ((star S : Subalgebra R A) : Set A) = star
 (S : Set A)
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star (S : Subalgebra R A) : ((star S : Subalgebra R A) : Set A) = star (S : Set A) :=
  rfl
/-
**Subalgebra.star_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：star_mono : Monotone (star : Subalgebra R A -> Subalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_mono : Monotone (star : Subalgebra R A → Subalgebra R A) := fun _ _ h _ hx => h hx

variable (R) in
/-- The star operation on `Subalgebra` commutes with `Algebra.adjoin`. -/
/-
**Subalgebra.star_adjoin_comm** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：star_adjoin_comm (s : Set A) : star (Algebra.adjoin R s) = Algebra.adjoin 
R (star s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Subalgebra.star_mono`：star_mono : Monotone (star : Subalgebra R A -> Sub
algebra R A)

--- 原说明 ---
The star operation on `Subalgebra` commutes with `Algebra.adjoin`.
-/
theorem star_adjoin_comm (s : Set A) : star (Algebra.adjoin R s) = Algebra.adjoin R (star s) :=
  have : ∀ t : Set A, Algebra.adjoin R (star t) ≤ star (Algebra.adjoin R t) := fun _ =>
    Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin hx
  le_antisymm (by simpa only [star_star] using Subalgebra.star_mono (this (star s))) (this s)

/-- The `StarSubalgebra` obtained from `S : Subalgebra R A` by taking the smallest subalgebra
containing both `S` and `star S`. -/
/-
**Subalgebra.starClosure** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：starClosure (S : Subalgebra R A) : StarSubalgebra R A where toSubalgebra
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `StarSubalgebra` obtained from `S : Subalgebra R A` by taking the smallest s
ubalgebra
containing both `S` and `star S`.
-/
def starClosure (S : Subalgebra R A) : StarSubalgebra R A where
  toSubalgebra := S ⊔ star S
  star_mem' := fun {a} ha => by
    simp only [Subalgebra.mem_carrier, ← (@Algebra.gi R A _ _ _).l_sup_u _ _] at *
    rw [← mem_star_iff _ a, star_adjoin_comm, sup_comm]
    simpa using ha

@[simp]
/-
**Subalgebra.coe_starClosure** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_starClosure (S : Subalgebra R A) : (S.starClosure : Set A) = (S ⊔ star
 S : Subalgebra R A)
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_starClosure (S : Subalgebra R A) :
    (S.starClosure : Set A) = (S ⊔ star S : Subalgebra R A) := rfl

@[simp]
/-
**Subalgebra.mem_starClosure** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_starClosure (S : Subalgebra R A) {x : A} : x in S.starClosure ↔ x in S
 ⊔ star S
参数：S : Subalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_starClosure (S : Subalgebra R A) {x : A} :
    x ∈ S.starClosure ↔ x ∈ S ⊔ star S := Iff.rfl
/-
**Subalgebra.starClosure_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：starClosure_toSubalgebra (S : Subalgebra R A) : S.starClosure.toSubalgebra
 = S ⊔ star S
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem starClosure_toSubalgebra (S : Subalgebra R A) :
    S.starClosure.toSubalgebra = S ⊔ star S := rfl
/-
**Subalgebra.starClosure_le** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：starClosure_le {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} (h : S₁ <= 
S₂.toSubalgebra) : S₁.starClosure <= S₂
参数：h : S₁ <= S₂.toSubalgebra。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StarSubalgebra.toSubalgebra_le_iff`：toSubalgebra_le_iff {S₁ S₂ : StarSub
algebra R A} : S₁.toSubalgebra <= S₂.toSubalgebra ↔ S₁ <= S₂
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `Subalgebra.mem_star_iff`：mem_star_iff (S : Subalgebra R A) (x : A) : x i
n star S ↔ star x in S
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem starClosure_le {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂.toSubalgebra) :
    S₁.starClosure ≤ S₂ :=
  StarSubalgebra.toSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)
/-
**Subalgebra.starClosure_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：starClosure_le_iff {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} : S₁.st
arClosure <= S₂ ↔ S₁ <= S₂.toSubalgebra
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Subalgebra.starClosure_le`：starClosure_le {S₁ : Subalgebra R A} {S₂ : St
arSubalgebra R A} (h : S₁ <= S₂.toSubalgebra) : S₁.starClosure <= S₂
-/
theorem starClosure_le_iff {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩

end Subalgebra

/-! ### The star subalgebra generated by a set -/


namespace StarAlgebra

open StarSubalgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]
variable (R)

/-- The minimal star subalgebra that contains `s`. -/
/-
**StarAlgebra.adjoin** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin (s : Set A) : StarSubalgebra R A
参数：s : Set A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal star subalgebra that contains `s`.
-/
def adjoin (s : Set A) : StarSubalgebra R A :=
  { Algebra.adjoin R (s ∪ star s) with
    star_mem' := fun hx => by
      rwa [Subalgebra.mem_carrier, ← Subalgebra.mem_star_iff, Subalgebra.star_adjoin_comm,
        Set.union_star, star_star, Set.union_comm] }
/-
**StarAlgebra.adjoin_eq_starClosure_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebr
a`。
形式化陈述：adjoin_eq_starClosure_adjoin (s : Set A) : adjoin R s = (Algebra.adjoin R 
s).starClosure
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.toSubalgebra_injective`：toSubalgebra_injective : Function
.Injective (toSubalgebra : StarSubalgebra R A -> Subalgebra R A)
· 使用定理 `Algebra.adjoin_union`：adjoin_union (s t : Set A) : adjoin R (s union t) 
= adjoin R s ⊔ adjoin R t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.star_adjoin_comm`：star_adjoin_comm (s : Set A) : star (Algebr
a.adjoin R s) = Algebra.adjoin R (star s)
-/
theorem adjoin_eq_starClosure_adjoin (s : Set A) : adjoin R s = (Algebra.adjoin R s).starClosure :=
  toSubalgebra_injective <|
    show Algebra.adjoin R (s ∪ star s) = Algebra.adjoin R s ⊔ star (Algebra.adjoin R s) from
      (Subalgebra.star_adjoin_comm R s).symm ▸ Algebra.adjoin_union s (star s)
/-
**StarAlgebra.adjoin_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin_toSubalgebra (s : Set A) : (adjoin R s).toSubalgebra = Algebra.adjo
in R (s union star s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjoin_toSubalgebra (s : Set A) :
    (adjoin R s).toSubalgebra = Algebra.adjoin R (s ∪ star s) := rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**StarAlgebra.subset_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：subset_adjoin (s : Set A) : s subseteq adjoin R s
参数：s : Set A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem subset_adjoin (s : Set A) : s ⊆ adjoin R s :=
  Set.subset_union_left.trans Algebra.subset_adjoin

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**StarAlgebra.star_subset_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：star_subset_adjoin (s : Set A) : star s subseteq adjoin R s
参数：s : Set A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem star_subset_adjoin (s : Set A) : star s ⊆ adjoin R s :=
  Set.subset_union_right.trans Algebra.subset_adjoin

@[aesop 80% (rule_sets := [SetLike])]
/-
**StarAlgebra.mem_adjoin_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：mem_adjoin_of_mem {s : Set A} {x : A} (hx : x in s) : x in adjoin R s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subseteq adjoin
 R s
-/
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x ∈ s) : x ∈ adjoin R s := subset_adjoin R s hx

@[simp]
/-
**StarAlgebra.self_mem_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：self_mem_adjoin_singleton (x : A) : x in adjoin R ({x} : Set A)
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  Algebra.subset_adjoin <| Set.mem_union_left _ (Set.mem_singleton x)
/-
**StarAlgebra.star_self_mem_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间 `StarAlge
bra`。
形式化陈述：star_self_mem_adjoin_singleton (x : A) : star x in adjoin R ({x} : Set A)
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `StarAlgebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A)
 : x in adjoin R ({x} : Set A)
-/
theorem star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : Set A) :=
  star_mem <| self_mem_adjoin_singleton R x

variable {R}
/-
**StarAlgebra.gc** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemiring R] [inst_1 : StarRing
 R] [inst_2 : Semiring A]   [inst_3 : Algebra R A] [inst_4 : StarRing A] [inst_5
 : StarModule R A],   GaloisConnection (StarAlgebra.adjoin R) SetLike.coe
参数：StarAlgebra.adjoin R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StarSubalgebra.toSubalgebra_le_iff`：toSubalgebra_le_iff {S₁ S₂ : StarSub
algebra R A} : S₁.toSubalgebra <= S₂.toSubalgebra ↔ S₁ <= S₂
· 使用定理 `StarAlgebra.adjoin_toSubalgebra`：adjoin_toSubalgebra (s : Set A) : (adjo
in R s).toSubalgebra = Algebra.adjoin R (s union star s)
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `StarSubalgebra.coe_toSubalgebra`：coe_toSubalgebra (S : StarSubalgebra R 
A) : (S.toSubalgebra : Set A) = S
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
protected theorem gc : GaloisConnection (adjoin R : Set A → StarSubalgebra R A) (↑) := by
  intro s S
  rw [← toSubalgebra_le_iff, adjoin_toSubalgebra, Algebra.adjoin_le_iff, coe_toSubalgebra]
  exact
    ⟨fun h => Set.subset_union_left.trans h, fun h =>
      Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩

/-- Galois insertion between `adjoin` and `coe`. -/
/-
**StarAlgebra.gi** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgebra`。
形式化陈述：{R : Type u_2} →   {A : Type u_3} →     [inst : CommSemiring R] →       [i
nst_1 : StarRing R] →         [inst_2 : Semiring A] →           [inst_3 : Algebr
a R A] →             [inst_4 : StarRing A] → [inst_5 : StarModule R A] → GaloisI
nsertion (StarAlgebra.adjoin R) SetLike.coe
参数：StarAlgebra.adjoin R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.gc`：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemiring R] 
[inst_1 : StarRing R] [inst_2 : Semiring A]   [inst_3 : Algebra R A] [inst_4 : S
tarR…

--- 原说明 ---
Galois insertion between `adjoin` and `coe`.
-/
protected def gi : GaloisInsertion (adjoin R : Set A → StarSubalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (StarAlgebra.gc.le_u_l s) hs
  gc := StarAlgebra.gc
  le_l_u S := (StarAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := StarSubalgebra.copy_eq _ _ _
/-
**StarAlgebra.adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin_le {S : StarSubalgebra R A} {s : Set A} (hs : s subseteq S) : adjoi
n R s <= S
参数：hs : s subseteq S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `StarAlgebra.gc`：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemiring R] 
[inst_1 : StarRing R] [inst_2 : Semiring A]   [inst_3 : Algebra R A] [inst_4 : S
tarR…
-/
theorem adjoin_le {S : StarSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  StarAlgebra.gc.l_le hs

@[simp]
/-
**StarAlgebra.adjoin_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin_le_iff {S : StarSubalgebra R A} {s : Set A} : adjoin R s <= S ↔ s s
ubseteq S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.gc`：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemiring R] 
[inst_1 : StarRing R] [inst_2 : Semiring A]   [inst_3 : Algebra R A] [inst_4 : S
tarR…
-/
theorem adjoin_le_iff {S : StarSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  StarAlgebra.gc _ _

@[gcongr]
/-
**StarAlgebra.adjoin_mono** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin_mono {s t : Set A} (H : s subseteq t) : adjoin R s <= adjoin R t
参数：H : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `StarAlgebra.gc`：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemiring R] 
[inst_1 : StarRing R] [inst_2 : Semiring A]   [inst_3 : Algebra R A] [inst_4 : S
tarR…
-/
theorem adjoin_mono {s t : Set A} (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  StarAlgebra.gc.monotone_l H

@[simp]
/-
**StarAlgebra.adjoin_eq** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin_eq (S : StarSubalgebra R A) : adjoin R (S : Set A) = S
参数：S : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `StarAlgebra.adjoin_le`：adjoin_le {S : StarSubalgebra R A} {s : Set A} (h
s : s subseteq S) : adjoin R s <= S
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `StarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subseteq adjoin
 R s
-/
lemma adjoin_eq (S : StarSubalgebra R A) : adjoin R (S : Set A) = S :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R (S : Set A))

open Submodule in
/-
**StarAlgebra.adjoin_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin_eq_span (s : Set A) : Subalgebra.toSubmodule (adjoin R s).toSubalge
bra = span R (Submonoid.closure (s union star s))
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAlgebra.adjoin_toSubalgebra`：adjoin_toSubalgebra (s : Set A) : (adjo
in R s).toSubalgebra = Algebra.adjoin R (s union star s)
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
-/
lemma adjoin_eq_span (s : Set A) :
    Subalgebra.toSubmodule (adjoin R s).toSubalgebra = span R (Submonoid.closure (s ∪ star s)) := by
  rw [adjoin_toSubalgebra, Algebra.adjoin_eq_span]

open Submodule in
/-
**StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `
StarAlgebra`。
形式化陈述：adjoin_nonUnitalStarSubalgebra_eq_span (s : NonUnitalStarSubalgebra R A) :
 (adjoin R (s : Set A)).toSubalgebra.toSubmodule = span R {1} ⊔ s.toSubmodule
参数：s : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StarAlgebra.adjoin_eq_span`：adjoin_eq_span (s : Set A) : Subalgebra.toSu
bmodule (adjoin R s).toSubalgebra = span R (Submonoid.closure (s union star s))
· 使用引理 `Submonoid.closure_eq_one_union`：closure_eq_one_union (s : Set M) : closu
re s = {(1 : M)} union (Subsemigroup.closure s : Set M)
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NonUnitalStarAlgebra.adjoin_eq_span`：adjoin_eq_span (s : Set A) : (adjoi
n R s).toSubmodule = Submodule.span R (Subsemigroup.closure (s union star s))
· 使用引理 `NonUnitalStarAlgebra.adjoin_eq`：adjoin_eq (s : NonUnitalStarSubalgebra R
 A) : adjoin R (s : Set A) = s
-/
lemma adjoin_nonUnitalStarSubalgebra_eq_span (s : NonUnitalStarSubalgebra R A) :
    (adjoin R (s : Set A)).toSubalgebra.toSubmodule = span R {1} ⊔ s.toSubmodule := by
  rw [adjoin_eq_span, Submonoid.closure_eq_one_union, span_union,
    ← NonUnitalStarAlgebra.adjoin_eq_span, NonUnitalStarAlgebra.adjoin_eq]
/-
**StarAlgebra._root_.Subalgebra.starClosure_eq_adjoin** 是 Mathlib 中的一个定理，位于命名空间 
`StarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subalgebra.starClosure_eq_adjoin (S : Subalgebra R A) :
    S.starClosure = adjoin R (S : Set A) :=
  le_antisymm (Subalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S ≤ S ⊔ star S))

/-- If some predicate holds for all `x ∈ (s : Set A)` and this predicate is closed under the
`algebraMap`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
@[elab_as_elim]
/-
**StarAlgebra.adjoin_induction** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin_induction {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop} (mem
 : forall (x) (h : x in s), p x (subset_adjoin R s h)) (algebraMap : forall r, p
 (algebraMap R _ r) (algebraMap_mem _ r)) (add : forall x y hx hy, p x hx -> p y
 hy -> p (x + y) (add_mem hx hy)) (mul : forall x y hx hy, p x hx -> p y hy -> p
 (x * y) (mul_mem hx hy)) (star : forall x hx, p x hx -> p (star x) (star_mem hx
)) {a : A} (ha : a in adjoin R s) : p a ha
参数：x : A；mem : forall (x) (h : x in s), p x (subset_adjoin R s h)；algebraMap : f
orall r, p (algebraMap R _ r) (algebraMap_mem _ r)；add : forall x y hx hy, p x h
x -> p y hy -> p (x + y) (add_mem hx hy)；mul : forall x y hx hy, p x hx -> p y h
y -> p (x * y) (mul_mem hx hy)；star : forall x hx, p x hx -> p (star x) (star_me
m hx)；ha : a in adjoin R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subseteq adjoin
 R s
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r

--- 原说明 ---
If some predicate holds for all `x ∈ (s : Set A)` and this predicate is closed u
nder the
`algebraMap`, addition, multiplication and star operations, then it holds for `a
 ∈ adjoin R s`.
-/
theorem adjoin_induction {s : Set A} {p : (x : A) → x ∈ adjoin R s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_adjoin R s h))
    (algebraMap : ∀ r, p (algebraMap R _ r) (algebraMap_mem _ r))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (star : ∀ x hx, p x hx → p (star x) (star_mem hx))
    {a : A} (ha : a ∈ adjoin R s) : p a ha := by
  refine Algebra.adjoin_induction (fun x hx ↦ ?_) algebraMap add mul ha
  push _ ∈ _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (Algebra.subset_adjoin (by simpa using Or.inl hx)) (mem _ hx)

@[elab_as_elim]
/-
**StarAlgebra.adjoin_induction** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin_induction {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop} (mem
 : forall (x) (h : x in s), p x (subset_adjoin R s h)) (algebraMap : forall r, p
 (algebraMap R _ r) (algebraMap_mem _ r)) (add : forall x y hx hy, p x hx -> p y
 hy -> p (x + y) (add_mem hx hy)) (mul : forall x y hx hy, p x hx -> p y hy -> p
 (x * y) (mul_mem hx hy)) (star : forall x hx, p x hx -> p (star x) (star_mem hx
)) {a : A} (ha : a in adjoin R s) : p a ha
参数：x : A；mem : forall (x) (h : x in s), p x (subset_adjoin R s h)；algebraMap : f
orall r, p (algebraMap R _ r) (algebraMap_mem _ r)；add : forall x y hx hy, p x h
x -> p y hy -> p (x + y) (add_mem hx hy)；mul : forall x y hx hy, p x hx -> p y h
y -> p (x * y) (mul_mem hx hy)；star : forall x hx, p x hx -> p (star x) (star_me
m hx)；ha : a in adjoin R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subseteq adjoin
 R s
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem adjoin_induction₂ {s : Set A} {p : (x y : A) → x ∈ adjoin R s → y ∈ adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_adjoin R s hx)
      (subset_adjoin R s hy))
    (algebraMap_both : ∀ r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂)
      (algebraMap_mem _ r₁) (algebraMap_mem _ r₂))
    (algebraMap_left : ∀ (r) (x) (hx : x ∈ s), p (algebraMap R A r) x (algebraMap_mem _ r)
      (subset_adjoin R s hx))
    (algebraMap_right : ∀ (r) (x) (hx : x ∈ s), p x (algebraMap R A r) (subset_adjoin R s hx)
      (algebraMap_mem _ r))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    (star_left : ∀ x y hx hy, p x y hx hy → p (star x) y (star_mem hx) hy)
    (star_right : ∀ x y hx hy, p x y hx hy → p x (star y) hx (star_mem hy))
    {a b : A} (ha : a ∈ adjoin R s) (hb : b ∈ adjoin R s) :
    p a b ha hb := by
  induction hb using adjoin_induction with
  | mem z hz => induction ha using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | algebraMap r =>
    induction ha using adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | star _ _ h => exact star_right _ _ _ _ h

/-- The difference with `StarSubalgebra.adjoin_induction` is that this acts on the subtype. -/
@[elab_as_elim]
/-
**StarAlgebra.adjoin_induction_subtype** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：adjoin_induction_subtype {s : Set A} {p : adjoin R s -> Prop} (a : adjoin 
R s) (mem : forall (x) (h : x in s), p ⟨x, subset_adjoin R s h⟩) (algebraMap : f
orall r, p (algebraMap R _ r)) (add : forall x y, p x -> p y -> p (x + y)) (mul 
: forall x y, p x -> p y -> p (x * y)) (star : forall x, p x -> p (star x)) : p 
a
参数：a : adjoin R s；mem : forall (x) (h : x in s), p ⟨x, subset_adjoin R s h⟩；alge
braMap : forall r, p (algebraMap R _ r)；add : forall x y, p x -> p y -> p (x + y
)；mul : forall x y, p x -> p y -> p (x * y)；star : forall x, p x -> p (star x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subseteq adjoin
 R s
· 使用定理 `StarAlgebra.adjoin_induction`：adjoin_induction {s : Set A} {p : (x : A) 
-> x in adjoin R s -> Prop} (mem : forall (x) (h : x in s), p x (subset_adjoin R
 s h)) (algebraMap…

--- 原说明 ---
The difference with `StarSubalgebra.adjoin_induction` is that this acts on the s
ubtype.
-/
theorem adjoin_induction_subtype {s : Set A} {p : adjoin R s → Prop} (a : adjoin R s)
    (mem : ∀ (x) (h : x ∈ s), p ⟨x, subset_adjoin R s h⟩) (algebraMap : ∀ r, p (algebraMap R _ r))
    (add : ∀ x y, p x → p y → p (x + y)) (mul : ∀ x y, p x → p y → p (x * y))
    (star : ∀ x, p x → p (star x)) : p a :=
  Subtype.recOn a fun b hb => by
    induction hb using adjoin_induction with
    | mem _ h => exact mem _ h
    | algebraMap _ => exact algebraMap _
    | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add _ _ h₁ h₂
    | star _ _ h => exact star _ h

variable (R)
/-
**StarAlgebra.adjoin_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `StarA
lgebra`。
形式化陈述：adjoin_le_centralizer_centralizer (s : Set A) : adjoin R s <= centralizer 
R (centralizer R s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StarSubalgebra.toSubalgebra_le_iff`：toSubalgebra_le_iff {S₁ S₂ : StarSub
algebra R A} : S₁.toSubalgebra <= S₂.toSubalgebra ↔ S₁ <= S₂
· 使用定理 `StarSubalgebra.centralizer_toSubalgebra`：centralizer_toSubalgebra (s : S
et A) : (centralizer R s).toSubalgebra = Subalgebra.centralizer R (s union star 
s)
· 使用定理 `StarAlgebra.adjoin_toSubalgebra`：adjoin_toSubalgebra (s : Set A) : (adjo
in R s).toSubalgebra = Algebra.adjoin R (s union star s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `StarMemClass.star_coe_eq`：StarMemClass.star_coe_eq {S α : Type*} [Involu
tiveStar α] [SetLike S α] [StarMemClass S α] (s : S) : star (s : Set α) = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Algebra.adjoin_le_centralizer_centralizer`：adjoin_le_centralizer_central
izer (s : Set A) : adjoin R s <= Subalgebra.centralizer R (Subalgebra.centralize
r R s)
-/
lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s ≤ centralizer R (centralizer R s) := by
  rw [← toSubalgebra_le_iff, centralizer_toSubalgebra, adjoin_toSubalgebra]
  convert! Algebra.adjoin_le_centralizer_centralizer R (s ∪ star s)
  rw [StarMemClass.star_coe_eq]
  simp

/-- If all elements of `s : Set A` commute pairwise and with elements of `star s`, then `adjoin R s`
is commutative. -/
/-
**StarAlgebra.isMulCommutative_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra`。
形式化陈述：isMulCommutative_adjoin {s : Set A} (hcomm : forall x in s, forall y in s,
 x * y = y * x) (hcomm_star : forall a in s, forall b in s, a * star b = star b 
* a) : IsMulCommutative (adjoin R s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x；hcomm_star : forall a in 
s, forall b in s, a * star b = star b * a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StarAlgebra.adjoin_le_centralizer_centralizer`：adjoin_le_centralizer_cen
tralizer (s : Set A) : adjoin R s <= centralizer R (centralizer R s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `Set.union_star_self_comm`：Set.union_star_self_comm (hcomm : forall x in 
s, forall y in s, y * x = x * y) (hcomm_star : forall x in s, forall y in s, y *
 star x = star…
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.coe_centralizer_centralizer`：coe_centralizer_centralizer 
(s : Set A) : (centralizer R (centralizer R s : Set A)) = (s union star s).centr
alizer.centralizer
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p

--- 原说明 ---
If all elements of `s : Set A` commute pairwise and with elements of `star s`, t
hen `adjoin R s`
is commutative.
-/
theorem isMulCommutative_adjoin {s : Set A} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) :
    IsMulCommutative (adjoin R s) := by
  have := adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ ↦ ?_
  have hcomm : ∀ a ∈ s ∪ star s, ∀ b ∈ s ∪ star s, a * b = b * a := fun a ha b hb ↦
    Set.union_star_self_comm (fun _ ha _ hb ↦ hcomm _ hb _ ha)
      (fun _ ha _ hb ↦ hcomm_star _ hb _ ha) b hb a ha
  apply this at h₁
  apply this at h₂
  rw [← SetLike.mem_coe, coe_centralizer_centralizer] at h₁ h₂
  exact Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise and also commute pairwise with elements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/-
**StarAlgebra.adjoinCommSemiringOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `StarAlgebra`
。
形式化陈述：adjoinCommSemiringOfComm {s : Set A} (hcomm : forall a in s, forall b in s
, a * b = b * a) (hcomm_star : forall a in s, forall b in s, a * star b = star b
 * a) : CommSemiring (adjoin R s)
参数：hcomm : forall a in s, forall b in s, a * b = b * a；hcomm_star : forall a in 
s, forall b in s, a * star b = star b * a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s : Set A}
 (hcomm : forall x in s, forall y in s, x * y = y * x) (hcomm_star : forall a in
 s, forall b in s, a * st…

--- 原说明 ---
If all elements of `s : Set A` commute pairwise and also commute pairwise with e
lements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible n
on-instances].
-/
abbrev adjoinCommSemiringOfComm {s : Set A}
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) :
    CommSemiring (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance
/-
**StarAlgebra.instIsMulCommutative_adjoin** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgebra
`。
形式化陈述：instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] [S
tarMemClass S A] (s : S) [IsMulCommutative s] : IsMulCommutative (adjoin R (s : 
Set A))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s : Set A}
 (hcomm : forall x in s, forall y in s, x * y = y * x) (hcomm_star : forall a in
 s, forall b in s, a * st…
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
-/
instance instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] [StarMemClass S A]
    (s : S) [IsMulCommutative s] : IsMulCommutative (adjoin R (s : Set A)) :=
  isMulCommutative_adjoin R
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂)
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ (star_mem h₂))

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise and also commute pairwise with elements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/-
**StarAlgebra.adjoinCommRingOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `StarAlgebra`。
形式化陈述：adjoinCommRingOfComm (R : Type u) {A : Type v} [CommRing R] [StarRing R] [
Ring A] [Algebra R A] [StarRing A] [StarModule R A] {s : Set A} (hcomm : forall 
a : A, a in s -> forall b : A, b in s -> a * b = b * a) (hcomm_star : forall a :
 A, a in s -> forall b : A, b in s -> a * star b = star b * a) : CommRing (adjoi
n R s)
参数：R : Type u；hcomm : forall a : A, a in s -> forall b : A, b in s -> a * b = b 
* a；hcomm_star : forall a : A, a in s -> forall b : A, b in s -> a * star b = st
ar b * a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all elements of `s : Set A` commute pairwise and also commute pairwise with e
lements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible n
on-instances].
-/
abbrev adjoinCommRingOfComm (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] {s : Set A}
    (hcomm : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * b = b * a)
    (hcomm_star : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * star b = star b * a) :
    CommRing (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

/-- The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
/-
**StarAlgebra.isMulCommutative_adjoin_singleton** 是 Mathlib 中的一个实例，位于命名空间 `StarA
lgebra`。
形式化陈述：isMulCommutative_adjoin_singleton (x : A) [IsStarNormal x] : IsMulCommutat
ive (adjoin R ({x} : Set A))
参数：x : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s : Set A}
 (hcomm : forall x in s, forall y in s, x * y = y * x) (hcomm_star : forall a in
 s, forall b in s, a * st…

--- 原说明 ---
The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` 
is commutative
if `x` is normal.
-/
instance isMulCommutative_adjoin_singleton (x : A) [IsStarNormal x] :
    IsMulCommutative (adjoin R ({x} : Set A)) :=
  isMulCommutative_adjoin R (by grind) (by grind)

open scoped IsMulCommutative in
/-- The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
@[deprecated isMulCommutative_adjoin_singleton (since := "2026-03-11")]
/-
**StarAlgebra.adjoinCommSemiringOfIsStarNormal** 是 Mathlib 中的一个实例，位于命名空间 `StarAl
gebra`。
形式化陈述：adjoinCommSemiringOfIsStarNormal (x : A) [IsStarNormal x] : CommSemiring (
adjoin R ({x} : Set A))
参数：x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` 
is commutative
if `x` is normal.
-/
instance adjoinCommSemiringOfIsStarNormal (x : A) [IsStarNormal x] :
    CommSemiring (adjoin R ({x} : Set A)) :=
  have := isMulCommutative_adjoin_singleton R x
  inferInstance

open scoped IsMulCommutative in
/-- The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
@[deprecated isMulCommutative_adjoin_singleton (since := "2026-03-11")]
/-
**StarAlgebra.adjoinCommRingOfIsStarNormal** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgebr
a`。
形式化陈述：adjoinCommRingOfIsStarNormal (R : Type u) {A : Type v} [CommRing R] [StarR
ing R] [Ring A] [Algebra R A] [StarRing A] [StarModule R A] (x : A) [IsStarNorma
l x] : CommRing (adjoin R ({x} : Set A))
参数：R : Type u；x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` 
is commutative
if `x` is normal.
-/
instance adjoinCommRingOfIsStarNormal (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] (x : A) [IsStarNormal x] :
    CommRing (adjoin R ({x} : Set A)) :=
  have := isMulCommutative_adjoin_singleton R x
  inferInstance

end StarAlgebra

/-! ### Complete lattice structure -/

namespace StarSubalgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-
**StarSubalgebra.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：completeLattice : CompleteLattice (StarSubalgebra R A) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance completeLattice : CompleteLattice (StarSubalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice StarAlgebra.gi
  bot := { toSubalgebra := ⊥, star_mem' := fun ⟨r, hr⟩ => ⟨star r, hr ▸ algebraMap_star_comm _⟩ }
  bot_le S := (bot_le : ⊥ ≤ S.toSubalgebra)
/-
**StarSubalgebra.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
形式化陈述：inhabited : Inhabited (StarSubalgebra R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (StarSubalgebra R A) :=
  ⟨⊤⟩

@[simp, norm_cast]
/-
**StarSubalgebra.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_top : (↑(⊤ : StarSubalgebra R A) : Set A) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : (↑(⊤ : StarSubalgebra R A) : Set A) = Set.univ :=
  rfl

@[simp]
/-
**StarSubalgebra.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_top {x : A} : x in (⊤ : StarSubalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top {x : A} : x ∈ (⊤ : StarSubalgebra R A) :=
  Set.mem_univ x

@[simp]
/-
**StarSubalgebra.top_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：top_toSubalgebra : (⊤ : StarSubalgebra R A).toSubalgebra = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem top_toSubalgebra : (⊤ : StarSubalgebra R A).toSubalgebra = ⊤ := by ext; simp
-- Porting note: Lean can no longer prove this by `rfl`, it times out

@[simp]
/-
**StarSubalgebra.toSubalgebra_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：toSubalgebra_eq_top {S : StarSubalgebra R A} : S.toSubalgebra = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `StarSubalgebra.toSubalgebra_injective`：toSubalgebra_injective : Function
.Injective (toSubalgebra : StarSubalgebra R A -> Subalgebra R A)
· 使用定理 `StarSubalgebra.top_toSubalgebra`：top_toSubalgebra : (⊤ : StarSubalgebra 
R A).toSubalgebra = ⊤
-/
theorem toSubalgebra_eq_top {S : StarSubalgebra R A} : S.toSubalgebra = ⊤ ↔ S = ⊤ :=
  StarSubalgebra.toSubalgebra_injective.eq_iff' top_toSubalgebra
/-
**StarSubalgebra.mem_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_sup_left {S T : StarSubalgebra R A} : forall {x : A}, x in S -> x in S
 ⊔ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem mem_sup_left {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
  have : S ≤ S ⊔ T := le_sup_left; (this ·)
/-
**StarSubalgebra.mem_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_sup_right {S T : StarSubalgebra R A} : forall {x : A}, x in T -> x in 
S ⊔ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem mem_sup_right {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
  have : T ≤ S ⊔ T := le_sup_right; (this ·)
/-
**StarSubalgebra.mul_mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mul_mem_sup {S T : StarSubalgebra R A} {x y : A} (hx : x in S) (hy : y in 
T) : x * y in S ⊔ T
参数：hx : x in S；hy : y in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `StarSubalgebra.mem_sup_left`：mem_sup_left {S T : StarSubalgebra R A} : f
orall {x : A}, x in S -> x in S ⊔ T
· 使用定理 `StarSubalgebra.mem_sup_right`：mem_sup_right {S T : StarSubalgebra R A} :
 forall {x : A}, x in T -> x in S ⊔ T
-/
theorem mul_mem_sup {S T : StarSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)
/-
**StarSubalgebra.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：map_sup (f : A ->⋆ₐ[R] B) (S T : StarSubalgebra R A) : map f (S ⊔ T) = map
 f S ⊔ map f T
参数：f : A ->⋆ₐ[R] B；S T : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `StarSubalgebra.gc_map_comap`：gc_map_comap (f : A ->⋆ₐ[R] B) : GaloisConn
ection (map f) (comap f)
-/
theorem map_sup (f : A →⋆ₐ[R] B) (S T : StarSubalgebra R A) : map f (S ⊔ T) = map f S ⊔ map f T :=
  (StarSubalgebra.gc_map_comap f).l_sup
/-
**StarSubalgebra.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：map_inf (f : A ->⋆ₐ[R] B) (hf : Function.Injective f) (S T : StarSubalgebr
a R A) : map f (S ⊓ T) = map f S ⊓ map f T
参数：f : A ->⋆ₐ[R] B；hf : Function.Injective f；S T : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (f : A →⋆ₐ[R] B) (hf : Function.Injective f) (S T : StarSubalgebra R A) :
    map f (S ⊓ T) = map f S ⊓ map f T := SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
/-
**StarSubalgebra.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_inf (S T : StarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) inte
r T
参数：S T : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (S T : StarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) ∩ T :=
  rfl

@[simp]
/-
**StarSubalgebra.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_inf {S T : StarSubalgebra R A} {x : A} : x in S ⊓ T ↔ x in S ∧ x in T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {S T : StarSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
/-
**StarSubalgebra.inf_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：inf_toSubalgebra (S T : StarSubalgebra R A) : (S ⊓ T).toSubalgebra = S.toS
ubalgebra ⊓ T.toSubalgebra
参数：S T : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inf_toSubalgebra (S T : StarSubalgebra R A) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra := by
  ext; simp
-- Porting note: Lean can no longer prove this by `rfl`, it times out

@[simp, norm_cast]
/-
**StarSubalgebra.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s in S, 
↑s
参数：S : Set (StarSubalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
-/
theorem coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image

@[simp]
/-
**StarSubalgebra.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_sInf {S : Set (StarSubalgebra R A)} {x : A} : x in sInf S ↔ forall p i
n S, x in p
参数：StarSubalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarSubalgebra.coe_sInf`：coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sI
nf S) : Set A) = ⋂ s in S, ↑s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sInf {S : Set (StarSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
/-
**StarSubalgebra.sInf_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：sInf_toSubalgebra (S : Set (StarSubalgebra R A)) : (sInf S).toSubalgebra =
 sInf (StarSubalgebra.toSubalgebra '' S)
参数：S : Set (StarSubalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.coe_sInf`：coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sI
nf S) : Set A) = ⋂ s in S, ↑s
· 使用定理 `Algebra.coe_sInf`：coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set
 A) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_toSubalgebra (S : Set (StarSubalgebra R A)) :
    (sInf S).toSubalgebra = sInf (StarSubalgebra.toSubalgebra '' S) :=
  SetLike.coe_injective <| by simp

@[simp, norm_cast]
/-
**StarSubalgebra.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> StarSubalgebra R A} : (↑(⨅ i, S i) : Set A)
 = ⋂ i, S i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.coe_sInf`：coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sI
nf S) : Set A) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]

@[simp]
/-
**StarSubalgebra.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> StarSubalgebra R A} {x : A} : x in ⨅ i, S i
 ↔ forall i, x in S i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} {x : A} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]
/-
**StarSubalgebra.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : A ->⋆ₐ[R] B) (hf : Function.Injecti
ve f) (s : ι -> StarSubalgebra R A) : map f (iInf s) = ⨅ (i : ι), map f (s i)
参数：f : A ->⋆ₐ[R] B；hf : Function.Injective f；s : ι -> StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> StarSubalgebra R
 A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : A →⋆ₐ[R] B) (hf : Function.Injective f)
    (s : ι → StarSubalgebra R A) : map f (iInf s) = ⨅ (i : ι), map f (s i) := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[simp]
/-
**StarSubalgebra.iInf_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：iInf_toSubalgebra {ι : Sort*} (S : ι -> StarSubalgebra R A) : (⨅ i, S i).t
oSubalgebra = ⨅ i, (S i).toSubalgebra
参数：S : ι -> StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> StarSubalgebra R
 A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i
· 使用定理 `Algebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subalgebra R A} : (↑(⨅ 
i, S i) : Set A) = ⋂ i, S i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_toSubalgebra {ι : Sort*} (S : ι → StarSubalgebra R A) :
    (⨅ i, S i).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by simp
/-
**StarSubalgebra.bot_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：bot_toSubalgebra : (⊥ : StarSubalgebra R A).toSubalgebra = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_toSubalgebra : (⊥ : StarSubalgebra R A).toSubalgebra = ⊥ := rfl
/-
**StarSubalgebra.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_bot {x : A} : x in (⊥ : StarSubalgebra R A) ↔ x in Set.range (algebraM
ap R A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_bot {x : A} : x ∈ (⊥ : StarSubalgebra R A) ↔ x ∈ Set.range (algebraMap R A) := Iff.rfl

@[simp, norm_cast]
/-
**StarSubalgebra.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_bot : ((⊥ : StarSubalgebra R A) : Set A) = Set.range (algebraMap R A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : StarSubalgebra R A) : Set A) = Set.range (algebraMap R A) := rfl
/-
**StarSubalgebra.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`。
形式化陈述：eq_top_iff {S : StarSubalgebra R A} : S = ⊤ ↔ forall x : A, x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.mem_top`：mem_top {x : A} : x in (⊤ : StarSubalgebra R A)
· 使用定理 `StarSubalgebra.ext`：ext {S T : StarSubalgebra R A} (h : forall x : A, x 
in S ↔ x in T) : S = T
-/
theorem eq_top_iff {S : StarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top,
  fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

end StarSubalgebra

namespace StarAlgHom

open StarSubalgebra StarAlgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A]
variable [Semiring B] [Algebra R B] [StarRing B]

section
variable [StarModule R A]

/-
**StarAlgHom.ext_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：ext_adjoin {s : Set A} [FunLike F (adjoin R s) B] [AlgHomClass F R (adjoin
 R s) B] [StarHomClass F (adjoin R s) B] {f g : F} (h : forall x : adjoin R s, (
x : A) in s -> f x = g x) : f = g
参数：adjoin R s；adjoin R s；adjoin R s；h : forall x : adjoin R s, (x : A) in s -> f
 x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `StarAlgebra.adjoin_induction_subtype`：adjoin_induction_subtype {s : Set 
A} {p : adjoin R s -> Prop} (a : adjoin R s) (mem : forall (x) (h : x in s), p ⟨
x, subset_adjoin R s h⟩) (…
· 使用定理 `StarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subseteq adjoin
 R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
-/
theorem ext_adjoin {s : Set A} [FunLike F (adjoin R s) B]
    [AlgHomClass F R (adjoin R s) B] [StarHomClass F (adjoin R s) B] {f g : F}
    (h : ∀ x : adjoin R s, (x : A) ∈ s → f x = g x) : f = g := by
  refine DFunLike.ext f g fun a =>
    adjoin_induction_subtype (p := fun y => f y = g y) a (fun x hx => ?_) (fun r => ?_)
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) fun x hx => ?_
  · exact h ⟨x, subset_adjoin R s hx⟩ hx
  · simp only [AlgHomClass.commutes]
  · simp only [map_add, map_add, hx, hy]
  · simp only [map_mul, map_mul, hx, hy]
  · simp only [map_star, hx]
/-
**StarAlgHom.ext_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：ext_adjoin_singleton {a : A} [FunLike F (adjoin R ({a} : Set A)) B] [AlgHo
mClass F R (adjoin R ({a} : Set A)) B] [StarHomClass F (adjoin R ({a} : Set A)) 
B] {f g : F} (h : f ⟨a, self_mem_adjoin_singleton R a⟩ = g ⟨a, self_mem_adjoin_s
ingleton R a⟩) : f = g
参数：adjoin R ({a} : Set A)；adjoin R ({a} : Set A)；adjoin R ({a} : Set A)；h : f ⟨a
, self_mem_adjoin_singleton R a⟩ = g ⟨a, self_mem_adjoin_singleton R a⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A)
 : x in adjoin R ({x} : Set A)
· 使用定理 `StarAlgHom.ext_adjoin`：ext_adjoin {s : Set A} [FunLike F (adjoin R s) B]
 [AlgHomClass F R (adjoin R s) B] [StarHomClass F (adjoin R s) B] {f g : F} (h :
 forall x :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem ext_adjoin_singleton {a : A} [FunLike F (adjoin R ({a} : Set A)) B]
    [AlgHomClass F R (adjoin R ({a} : Set A)) B] [StarHomClass F (adjoin R ({a} : Set A)) B]
    {f g : F} (h : f ⟨a, self_mem_adjoin_singleton R a⟩ = g ⟨a, self_mem_adjoin_singleton R a⟩) :
    f = g :=
  ext_adjoin fun x hx =>
    (show x = ⟨a, self_mem_adjoin_singleton R a⟩ from
          Subtype.ext <| Set.mem_singleton_iff.mp hx).symm ▸
      h

variable [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B] (f g : F)

/-- The equalizer of two star `R`-algebra homomorphisms. -/
/-
**StarAlgHom.equalizer** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：equalizer : StarSubalgebra R A where toSubalgebra
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer of two star `R`-algebra homomorphisms.
-/
def equalizer : StarSubalgebra R A where
  toSubalgebra := AlgHom.equalizer (f : A →ₐ[R] B) g
  star_mem' {a} (ha : f a = g a) := by simpa only [← map_star] using! congrArg star ha

@[simp]
/-
**StarAlgHom.mem_equalizer** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：mem_equalizer (x : A) : x in StarAlgHom.equalizer f g ↔ f x = g x
参数：x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_equalizer (x : A) : x ∈ StarAlgHom.equalizer f g ↔ f x = g x :=
  Iff.rfl
/-
**StarAlgHom.adjoin_le_equalizer** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：adjoin_le_equalizer {s : Set A} (h : s.EqOn f g) : adjoin R s <= StarAlgHo
m.equalizer f g
参数：h : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.adjoin_le`：adjoin_le {S : StarSubalgebra R A} {s : Set A} (h
s : s subseteq S) : adjoin R s <= S
-/
theorem adjoin_le_equalizer {s : Set A} (h : s.EqOn f g) : adjoin R s ≤ StarAlgHom.equalizer f g :=
  adjoin_le h
/-
**StarAlgHom.ext_of_adjoin_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃f g : F⦄ (hs : s.Eq
On f g) : f = g
参数：h : adjoin R s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `StarAlgHom.adjoin_le_equalizer`：adjoin_le_equalizer {s : Set A} (h : s.E
qOn f g) : adjoin R s <= StarAlgHom.equalizer f g
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃f g : F⦄ (hs : s.EqOn f g) : f = g :=
  DFunLike.ext f g fun _x => StarAlgHom.adjoin_le_equalizer f g hs <| h.symm ▸ trivial


variable [StarModule R B]
/-
**StarAlgHom.map_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：map_adjoin (f : A ->⋆ₐ[R] B) (s : Set A) : map f (adjoin R s) = adjoin R (
f '' s)
参数：f : A ->⋆ₐ[R] B；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_comm_of_u_comm`：l_comm_of_u_comm {X : Type*} [Preorde
r X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [PartialOrder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `StarSubalgebra.gc_map_comap`：gc_map_comap (f : A ->⋆ₐ[R] B) : GaloisConn
ection (map f) (comap f)
· 使用定理 `StarAlgebra.gc`：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemiring R] 
[inst_1 : StarRing R] [inst_2 : Semiring A]   [inst_3 : Algebra R A] [inst_4 : S
tarR…
-/
theorem map_adjoin (f : A →⋆ₐ[R] B) (s : Set A) :
    map f (adjoin R s) = adjoin R (f '' s) :=
  GaloisConnection.l_comm_of_u_comm Set.image_preimage (gc_map_comap f) StarAlgebra.gc
    StarAlgebra.gc fun _ => rfl

/-- Range of a `StarAlgHom` as a star subalgebra. -/
/-
**StarAlgHom.range** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：{R : Type u_2} →   {A : Type u_3} →     {B : Type u_4} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : Semiring A] →
             [inst_3 : Algebra R A] →               [inst_4 : StarRing A] →     
            [inst_5 : Semiring B] →                   [inst_6 : Algebra R B] →  
                   [inst_7 : StarRing B] → [inst_8 : StarModule R B] → (A →⋆ₐ[R]
 B) → StarSubalgebra R B
参数：A →⋆ₐ[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Range of a `StarAlgHom` as a star subalgebra.
-/
protected def range
    (φ : A →⋆ₐ[R] B) : StarSubalgebra R B where
  toSubalgebra := φ.toAlgHom.range
  star_mem' := by rintro _ ⟨b, rfl⟩; exact ⟨star b, map_star φ b⟩
/-
**StarAlgHom.range_eq_map_top** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：range_eq_map_top (φ : A ->⋆ₐ[R] B) : φ.range = (⊤ : StarSubalgebra R A).ma
p φ
参数：φ : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.ext`：ext {S T : StarSubalgebra R A} (h : forall x : A, x 
in S ↔ x in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.top_toSubalgebra`：top_toSubalgebra : (⊤ : StarSubalgebra 
R A).toSubalgebra = ⊤
-/
theorem range_eq_map_top (φ : A →⋆ₐ[R] B) : φ.range = (⊤ : StarSubalgebra R A).map φ :=
  StarSubalgebra.ext fun x =>
    ⟨by rintro ⟨a, ha⟩; exact ⟨a, by simp, ha⟩, by rintro ⟨a, -, ha⟩; exact ⟨a, ha⟩⟩

end

variable [StarModule R B]
/-- Restriction of the codomain of a `StarAlgHom` to a star subalgebra containing the range. -/
/-
**StarAlgHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：{R : Type u_2} →   {A : Type u_3} →     {B : Type u_4} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : Semiring A] →
             [inst_3 : Algebra R A] →               [inst_4 : StarRing A] →     
            [inst_5 : Semiring B] →                   [inst_6 : Algebra R B] →  
                   [inst_7 : StarRing B] →                       [inst_8 : StarM
odule R B] →                         (f : A →⋆ₐ[R] B) → (S : StarSubalgebra R B)
 → (∀ (x : A), f x ∈ S) → A →⋆ₐ[R] ↥S
参数：f : A →⋆ₐ[R] B；S : StarSubalgebra R B；∀ (x : A), f x ∈ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of the codomain of a `StarAlgHom` to a star subalgebra containing th
e range.
-/
protected def codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : ∀ x, f x ∈ S) :
    A →⋆ₐ[R] S where
  toAlgHom := AlgHom.codRestrict f.toAlgHom S.toSubalgebra hf
  map_star' := fun x => Subtype.ext (map_star f x)

@[simp]
/-
**StarAlgHom.coe_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：coe_codRestrict (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : forall x,
 f x in S) (x : A) : ↑(f.codRestrict S hf x) = f x
参数：f : A ->⋆ₐ[R] B；S : StarSubalgebra R B；hf : forall x, f x in S；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(f.codRestrict S hf x) = f x :=
  rfl

@[simp]
/-
**StarAlgHom.subtype_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：subtype_comp_codRestrict (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : 
forall x : A, f x in S) : S.subtype.comp (f.codRestrict S hf) = f
参数：f : A ->⋆ₐ[R] B；S : StarSubalgebra R B；hf : forall x : A, f x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
· 使用定理 `StarAlgHom.coe_codRestrict`：coe_codRestrict (f : A ->⋆ₐ[R] B) (S : StarS
ubalgebra R B) (hf : forall x, f x in S) (x : A) : ↑(f.codRestrict S hf x) = f x
-/
theorem subtype_comp_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B)
    (hf : ∀ x : A, f x ∈ S) : S.subtype.comp (f.codRestrict S hf) = f :=
  StarAlgHom.ext <| coe_codRestrict _ S hf
/-
**StarAlgHom.injective_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：injective_codRestrict (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : for
all x : A, f x in S) : Function.Injective (StarAlgHom.codRestrict f S hf) ↔ Func
tion.Injective f
参数：f : A ->⋆ₐ[R] B；S : StarSubalgebra R B；hf : forall x : A, f x in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (StarAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/-- Restriction of the codomain of a `StarAlgHom` to its range. -/
/-
**StarAlgHom.rangeRestrict** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：rangeRestrict (f : A ->⋆ₐ[R] B) : A ->⋆ₐ[R] f.range
参数：f : A ->⋆ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of the codomain of a `StarAlgHom` to its range.
-/
def rangeRestrict (f : A →⋆ₐ[R] B) : A →⋆ₐ[R] f.range :=
  StarAlgHom.codRestrict f _ fun x => ⟨x, rfl⟩

/-- The `StarAlgEquiv` onto the range corresponding to an injective `StarAlgHom`. -/
@[simps]
/-
**StarAlgHom._root_.StarAlgEquiv.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgH
om`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `StarAlgEquiv` onto the range corresponding to an injective `StarAlgHom`.
-/
noncomputable def _root_.StarAlgEquiv.ofInjective (f : A →⋆ₐ[R] B)
    (hf : Function.Injective f) : A ≃⋆ₐ[R] f.range :=
  { AlgEquiv.ofInjective f.toAlgHom hf with
    toFun := f.rangeRestrict
    map_star' := fun a => Subtype.ext (map_star f a)
    map_smul' := fun r a => Subtype.ext (map_smul f r a) }
end StarAlgHom


section RestrictScalars

section Equiv

variable (R : Type*) {S A B : Type*} [CommSemiring R] [CommSemiring S]
  [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S] [Module S A]
  [Module S B] [Module R A] [Module R B] [IsScalarTower R S A] [IsScalarTower R S B]
  [Star A] [Star B]

/-- Restrict the scalar ring of a star algebra equivalence. -/
@[simps]
/-
**StarAlgEquiv.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StarAlgEquiv.restrictScalars (f : A ≃⋆ₐ[S] B) : A ≃⋆ₐ[R] B
参数：f : A ≃⋆ₐ[S] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the scalar ring of a star algebra equivalence.
-/
def StarAlgEquiv.restrictScalars (f : A ≃⋆ₐ[S] B) : A ≃⋆ₐ[R] B :=
  { (f : A →ₗ[S] B).restrictScalars R, f with
    toFun := f }
/-
**StarAlgEquiv.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarAlgEquiv.restrictScalars_injective : Function.Injective (StarAlgEquiv.
restrictScalars R : (A ≃⋆ₐ[S] B) -> A ≃⋆ₐ[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgEquiv.ext`：ext {f g : A ≃⋆ₐ[R] B} (h : forall a, f a = g a) : f =
 g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem StarAlgEquiv.restrictScalars_injective :
    Function.Injective (StarAlgEquiv.restrictScalars R : (A ≃⋆ₐ[S] B) → A ≃⋆ₐ[R] B) :=
  fun _ _ h => ext (DFunLike.congr_fun h ·)

@[simp]
/-
**StarAlgEquiv.toNonUnitalStarAlgHom_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：StarAlgEquiv.toNonUnitalStarAlgHom_restrictScalars (e : A ≃⋆ₐ[S] B) : (e.r
estrictScalars R).toNonUnitalStarAlgHom = e.toNonUnitalStarAlgHom.restrictScalar
s R
参数：e : A ≃⋆ₐ[S] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StarAlgEquiv.toNonUnitalStarAlgHom_restrictScalars (e : A ≃⋆ₐ[S] B) :
    (e.restrictScalars R).toNonUnitalStarAlgHom = e.toNonUnitalStarAlgHom.restrictScalars R :=
  rfl

end Equiv

section Unital

variable (R : Type*) {S A B : Type*} [CommSemiring R]
  [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S] [Algebra S A] [Algebra S B]
  [Algebra R A] [Algebra R B] [IsScalarTower R S A] [IsScalarTower R S B] [Star A] [Star B]

@[simps!]
/-
**StarAlgHom.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StarAlgHom.restrictScalars (f : A ->⋆ₐ[S] B) : A ->⋆ₐ[R] B where toAlgHom
参数：f : A ->⋆ₐ[S] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def StarAlgHom.restrictScalars (f : A →⋆ₐ[S] B) : A →⋆ₐ[R] B where
  toAlgHom := f.toAlgHom.restrictScalars R
  map_star' := map_star f
/-
**StarAlgHom.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarAlgHom.restrictScalars_injective : Function.Injective (StarAlgHom.rest
rictScalars R : (A ->⋆ₐ[S] B) -> A ->⋆ₐ[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem StarAlgHom.restrictScalars_injective :
    Function.Injective (StarAlgHom.restrictScalars R : (A →⋆ₐ[S] B) → A →⋆ₐ[R] B) :=
  fun f g h => StarAlgHom.ext fun x =>
    show f.restrictScalars R x = g.restrictScalars R x from DFunLike.congr_fun h x

@[simp]
/-
**StarAlgEquiv.toStarAlgHom_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StarAlgEquiv.toStarAlgHom_restrictScalars (e : A ≃⋆ₐ[S] B) : (e.restrictSc
alars R).toStarAlgHom = e.toStarAlgHom.restrictScalars R
参数：e : A ≃⋆ₐ[S] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StarAlgEquiv.toStarAlgHom_restrictScalars (e : A ≃⋆ₐ[S] B) :
    (e.restrictScalars R).toStarAlgHom = e.toStarAlgHom.restrictScalars R :=
  rfl

end Unital

end RestrictScalars

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A]

/-- Turn a non-unital star subalgebra containing `1` into a `StarSubalgebra`. -/
/-
**NonUnitalStarSubalgebra.toStarSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalStarSubalgebra.toStarSubalgebra (S : NonUnitalStarSubalgebra R A)
 (h1 : 1 in S) : StarSubalgebra R A where __
参数：S : NonUnitalStarSubalgebra R A；h1 : 1 in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a non-unital star subalgebra containing `1` into a `StarSubalgebra`.
-/
def NonUnitalStarSubalgebra.toStarSubalgebra (S : NonUnitalStarSubalgebra R A) (h1 : 1 ∈ S) :
    StarSubalgebra R A where
  __ := S
  one_mem' := h1
  algebraMap_mem' r :=
    (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1
/-
**StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra (S : StarSubalge
bra R A) : S.toNonUnitalStarSubalgebra.toStarSubalgebra S.one_mem' = S
参数：S : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.one_mem'`：∀ {M : Type u_3} [inst : MulOneClass M] (self : Subm
onoid M), 1 ∈ self.carrier
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra (S : StarSubalgebra R A) :
    S.toNonUnitalStarSubalgebra.toStarSubalgebra S.one_mem' = S := by cases S; rfl
/-
**NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra** 是 Mathlib
 中的一个引理，位于命名空间 ``。
形式化陈述：NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra (S : No
nUnitalStarSubalgebra R A) (h1 : (1 : A) in S) : (S.toStarSubalgebra h1).toNonUn
italStarSubalgebra = S
参数：S : NonUnitalStarSubalgebra R A；h1 : (1 : A) in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) (h1 : (1 : A) ∈ S) :
    (S.toStarSubalgebra h1).toNonUnitalStarSubalgebra = S := by
  cases S; rfl

variable (R)
/-
**NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin (s : Set A) : adjoin R s
 <= (StarAlgebra.adjoin R s).toNonUnitalStarSubalgebra
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.adjoin_le`：adjoin_le {S : NonUnitalStarSubalgebra R
 A} {s : Set A} (hs : s subseteq S) : adjoin R s <= S
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `StarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subseteq adjoin
 R s
-/
lemma NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin (s : Set A) :
    adjoin R s ≤ (StarAlgebra.adjoin R s).toNonUnitalStarSubalgebra :=
  adjoin_le <| StarAlgebra.subset_adjoin R s
/-
**StarAlgebra.adjoin_nonUnitalStarSubalgebra** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StarAlgebra.adjoin_nonUnitalStarSubalgebra (s : Set A) : adjoin R (NonUnit
alStarAlgebra.adjoin R s : Set A) = adjoin R s
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `StarAlgebra.adjoin_le`：adjoin_le {S : StarSubalgebra R A} {s : Set A} (h
s : s subseteq S) : adjoin R s <= S
· 使用引理 `NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin`：NonUnitalStarAlgebra.
adjoin_le_starAlgebra_adjoin (s : Set A) : adjoin R s <= (StarAlgebra.adjoin R s
).toNonUnitalStarSubalgebra
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `NonUnitalStarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subset
eq adjoin R s
· 使用定理 `StarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subseteq adjoin
 R s
-/
lemma StarAlgebra.adjoin_nonUnitalStarSubalgebra (s : Set A) :
    adjoin R (NonUnitalStarAlgebra.adjoin R s : Set A) = adjoin R s :=
  le_antisymm
    (adjoin_le <| NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin R s)
    (adjoin_le <| (NonUnitalStarAlgebra.subset_adjoin R s).trans <| subset_adjoin R _)

namespace StarSubalgebra

section directed

variable {R}

/-
**StarSubalgebra.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra`
。
形式化陈述：coe_iSup_of_directed {ι : Type*} [Nonempty ι] {S : ι -> StarSubalgebra R A
} (dir : Directed (· <= ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A)
参数：dir : Directed (· <= ·) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalStarSubalgebra.coe_iSup_of_directed`：coe_iSup_of_directed [None
mpty ι] {S : ι -> NonUnitalStarSubalgebra R A} (dir : Directed (· <= ·) S) : ↑(i
Sup S) = ⋃ i, (S i : Set A)
· 使用定理 `NonUnitalSubsemiring.mul_mem'`：∀ {R : Type u} [inst : NonUnitalNonAssocS
emiring R] (self : NonUnitalSubsemiring R) {a b : R},   a ∈ self.carrier → b ∈ s
elf.carrier → a * b…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `AddSubsemigroup.add_mem'`：∀ {M : Type u_3} [inst : Add M] (self : AddSub
semigroup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.car
rier
· 使用定理 `AddSubmonoid.zero_mem'`：∀ {M : Type u_3} [inst : AddZeroClass M] (self :
 AddSubmonoid M), 0 ∈ self.carrier
· 使用定理 `NonUnitalStarSubalgebra.star_mem'`：∀ {R : Type u} {A : Type v} [inst : C
ommSemiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R 
A]   [inst_3 : Star A] …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
-/
theorem coe_iSup_of_directed {ι : Type*} [Nonempty ι] {S : ι → StarSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : StarSubalgebra R A :=
    { __ := NonUnitalStarSubalgebra.copy _ _ (NonUnitalStarSubalgebra.coe_iSup_of_directed
        (S := fun i ↦ (S i).toNonUnitalStarSubalgebra) dir).symm
      algebraMap_mem' x :=
        let ⟨i⟩ := ‹Nonempty ι›
        Set.mem_iUnion.mpr ⟨i, algebraMap_mem (S i) x⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set A)) i)
    (Set.iUnion_subset fun _ ↦ le_iSup S _)
  this.symm ▸ rfl
/-
**StarSubalgebra.isMulCommutative_iSup** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra
`。
形式化陈述：isMulCommutative_iSup {ι : Type*} [Nonempty ι] {S : ι -> StarSubalgebra R 
A} [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) : IsMulCo
mmutative (⨆ i, S i : StarSubalgebra R A)
参数：S i；dir : Directed (· <= ·) S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.coe_iSup_of_directed`：coe_iSup_of_directed {ι : Type*} [N
onempty ι] {S : ι -> StarSubalgebra R A} (dir : Directed (· <= ·) S) : ↑(iSup S)
 = ⋃ i, (S i : Set A)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Subalgebra.coe_iSup_of_directed`：coe_iSup_of_directed (dir : Directed (·
 <= ·) K) : ↑(iSup K) = ⋃ i, (K i : Set A)
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subalgebra.isMulCommutative_iSup`：isMulCommutative_iSup {S : ι -> Subalg
ebra R A} [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) : 
IsMulCommutative (⨆ i,…
-/
theorem isMulCommutative_iSup {ι : Type*} [Nonempty ι] {S : ι → StarSubalgebra R A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (· ≤ ·) S) :
    IsMulCommutative (⨆ i, S i : StarSubalgebra R A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subalgebra.coe_iSup_of_directed dir] using Subalgebra.isMulCommutative_iSup dir
/-
**StarSubalgebra.instIsMulCommutative_iSup** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalg
ebra`。
形式化陈述：instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirecte
dOrder ι] {S : ι ->o StarSubalgebra R A} [hS : forall i, IsMulCommutative (S i)]
 : IsMulCommutative (⨆ i, S i : StarSubalgebra R A)
参数：S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.isMulCommutative_iSup`：isMulCommutative_iSup {ι : Type*} 
[Nonempty ι] {S : ι -> StarSubalgebra R A} [hS : forall i, IsMulCommutative (S i
)] (dir : Directed (· <= ·…
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o StarSubalgebra R A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : StarSubalgebra R A) :=
  isMulCommutative_iSup S.monotone.directed_le

end directed

end StarSubalgebra

