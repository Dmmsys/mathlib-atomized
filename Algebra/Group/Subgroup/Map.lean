/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# `map` and `comap` for subgroups

We prove results about images and preimages of subgroups under group homomorphisms. The bundled
subgroups use bundled monoid homomorphisms.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `H` is a `Subgroup` of `G`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `Subgroup.comap H f` : the preimage of a subgroup `H` along the group homomorphism `f` is also a
  subgroup

* `Subgroup.map f H` : the image of a subgroup `H` along the group homomorphism `f` is also a
  subgroup

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Multiset Ring

open Function
open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']
variable {A : Type*} [AddGroup A]

namespace Subgroup

variable (H K : Subgroup G) {k : Set G}

open Set

variable {N : Type*} [Group N] {P : Type*} [Group P]

/-- The preimage of a subgroup along a monoid homomorphism is a subgroup. -/
@[to_additive
      /-- The preimage of an `AddSubgroup` along an `AddMonoid` homomorphism
      is an `AddSubgroup`. -/]
/-
**Subgroup.comap** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：comap {N : Type*} [Group N] (f : G ->* N) (H : Subgroup N) : Subgroup G
参数：f : G ->* N；H : Subgroup N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comap {N : Type*} [Group N] (f : G →* N) (H : Subgroup N) : Subgroup G :=
  { H.toSubmonoid.comap f with
    carrier := f ⁻¹' H
    inv_mem' := fun {a} ha => show f a⁻¹ ∈ H by rw [f.map_inv]; exact H.inv_mem ha }

@[to_additive (attr := simp)]
/-
**Subgroup.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_comap (K : Subgroup N) (f : G ->* N) : (K.comap f : Set G) = f ⁻¹' K
参数：K : Subgroup N；f : G ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (K : Subgroup N) (f : G →* N) : (K.comap f : Set G) = f ⁻¹' K :=
  rfl

@[to_additive (attr := simp)]
/-
**Subgroup.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_comap {K : Subgroup N} {f : G ->* N} {x : G} : x in K.comap f ↔ f x in
 K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {K : Subgroup N} {f : G →* N} {x : G} : x ∈ K.comap f ↔ f x ∈ K :=
  Iff.rfl

@[to_additive (attr := gcongr)]
/-
**Subgroup.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <= K' -> comap f K <= com
ap f K'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem comap_mono {f : G →* N} {K K' : Subgroup N} : K ≤ K' → comap f K ≤ comap f K' :=
  preimage_mono

@[to_additive]
/-
**Subgroup.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_comap (K : Subgroup P) (g : N ->* P) (f : G ->* N) : (K.comap g).com
ap f = K.comap (g.comp f)
参数：K : Subgroup P；g : N ->* P；f : G ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (K : Subgroup P) (g : N →* P) (f : G →* N) :
    (K.comap g).comap f = K.comap (g.comp f) :=
  rfl

@[to_additive (attr := simp)]
/-
**Subgroup.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_id (K : Subgroup N) : K.comap (MonoidHom.id _) = K
参数：K : Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_id (K : Subgroup N) : K.comap (MonoidHom.id _) = K := by
  ext
  rfl

@[simp]
/-
**Subgroup.toAddSubgroup_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：toAddSubgroup_comap {G₂ : Type*} [Group G₂] (f : G ->* G₂) (s : Subgroup G
₂) : s.toAddSubgroup.comap (MonoidHom.toAdditive f) = Subgroup.toAddSubgroup (s.
comap f)
参数：f : G ->* G₂；s : Subgroup G₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubgroup_comap {G₂ : Type*} [Group G₂] (f : G →* G₂) (s : Subgroup G₂) :
    s.toAddSubgroup.comap (MonoidHom.toAdditive f) = Subgroup.toAddSubgroup (s.comap f) := rfl

@[simp]
/-
**Subgroup._root_.AddSubgroup.toSubgroup_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddSubgroup.toSubgroup_comap {A A₂ : Type*} [AddGroup A] [AddGroup A₂]
    (f : A →+ A₂) (s : AddSubgroup A₂) :
    s.toSubgroup.comap (AddMonoidHom.toMultiplicative f) = AddSubgroup.toSubgroup (s.comap f) := rfl

/-- The image of a subgroup along a monoid homomorphism is a subgroup. -/
@[to_additive
      /-- The image of an `AddSubgroup` along an `AddMonoid` homomorphism
      is an `AddSubgroup`. -/]
/-
**Subgroup.map** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：map (f : G ->* N) (H : Subgroup G) : Subgroup N
参数：f : G ->* N；H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : G →* N) (H : Subgroup G) : Subgroup N :=
  { H.toSubmonoid.map f with
    carrier := f '' H
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, H.inv_mem hx, f.map_inv x⟩ }

@[to_additive (attr := simp)]
/-
**Subgroup.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_map (f : G ->* N) (K : Subgroup G) : (K.map f : Set N) = f '' K
参数：f : G ->* N；K : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : G →* N) (K : Subgroup G) : (K.map f : Set N) = f '' K :=
  rfl

@[to_additive (attr := simp)]
/-
**Subgroup.map_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_toSubmonoid (f : G ->* G') (K : Subgroup G) : (Subgroup.map f K).toSub
monoid = Submonoid.map f K.toSubmonoid
参数：f : G ->* G'；K : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_toSubmonoid (f : G →* G') (K : Subgroup G) :
    (Subgroup.map f K).toSubmonoid = Submonoid.map f K.toSubmonoid := rfl

@[to_additive (attr := simp)]
/-
**Subgroup.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_map {f : G ->* N} {K : Subgroup G} {y : N} : y in K.map f ↔ exists x i
n K, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map {f : G →* N} {K : Subgroup G} {y : N} : y ∈ K.map f ↔ ∃ x ∈ K, f x = y := Iff.rfl

@[to_additive]
/-
**Subgroup.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_map_of_mem (f : G ->* N) {K : Subgroup G} {x : G} (hx : x in K) : f x 
in K.map f
参数：f : G ->* N；hx : x in K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_map_of_mem (f : G →* N) {K : Subgroup G} {x : G} (hx : x ∈ K) : f x ∈ K.map f :=
  mem_image_of_mem f hx

@[to_additive]
/-
**Subgroup.apply_coe_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：apply_coe_mem_map (f : G ->* N) (K : Subgroup G) (x : K) : f x in K.map f
参数：f : G ->* N；K : Subgroup G；x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mem_map_of_mem`：mem_map_of_mem (f : G ->* N) {K : Subgroup G} {
x : G} (hx : x in K) : f x in K.map f
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem apply_coe_mem_map (f : G →* N) (K : Subgroup G) (x : K) : f x ∈ K.map f :=
  mem_map_of_mem f x.prop

@[to_additive (attr := gcongr)]
/-
**Subgroup.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_mono {f : G ->* N} {K K' : Subgroup G} : K <= K' -> map f K <= map f K
'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono {f : G →* N} {K K' : Subgroup G} : K ≤ K' → map f K ≤ map f K' :=
  image_mono

@[to_additive (attr := simp)]
/-
**Subgroup.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_id : K.map (MonoidHom.id G) = K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id : K.map (MonoidHom.id G) = K :=
  SetLike.coe_injective <| image_id _

@[to_additive]
/-
**Subgroup.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_map (g : N ->* P) (f : G ->* N) : (K.map f).map g = K.map (g.comp f)
参数：g : N ->* P；f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (g : N →* P) (f : G →* N) : (K.map f).map g = K.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _

@[to_additive (attr := simp)]
/-
**Subgroup.map_one_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_one_eq_bot : K.map (1 : G ->* N) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem map_one_eq_bot : K.map (1 : G →* N) = ⊥ :=
  eq_bot_iff.mpr <| by
    rintro x ⟨y, _, rfl⟩
    simp

@[to_additive]
/-
**Subgroup.mem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_map_equiv {f : G ≃* N} {K : Subgroup G} {x : N} : x in K.map f.toMonoi
dHom ↔ f.symm x in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
theorem mem_map_equiv {f : G ≃* N} {K : Subgroup G} {x : N} :
    x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K :=
  Set.mem_image_equiv

@[to_additive (attr := simp 1100)]
/-
**Subgroup.mem_map_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_map_iff_mem {f : G ->* N} (hf : Function.Injective f) {K : Subgroup G}
 {x : G} : f x in K.map f ↔ x in K
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
-/
theorem mem_map_iff_mem {f : G →* N} (hf : Function.Injective f) {K : Subgroup G} {x : G} :
    f x ∈ K.map f ↔ x ∈ K :=
  hf.mem_set_image

@[to_additive]
/-
**Subgroup.map_equiv_eq_comap_symm'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_equiv_eq_comap_symm' (f : G ≃* N) (K : Subgroup G) : K.map f.toMonoidH
om = K.comap f.symm.toMonoidHom
参数：f : G ≃* N；K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem map_equiv_eq_comap_symm' (f : G ≃* N) (K : Subgroup G) :
    K.map f.toMonoidHom = K.comap f.symm.toMonoidHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]
/-
**Subgroup.map_equiv_eq_comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_equiv_eq_comap_symm (f : G ≃* N) (K : Subgroup G) : K.map f = K.comap 
(G
参数：f : G ≃* N；K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_equiv_eq_comap_symm'`：map_equiv_eq_comap_symm' (f : G ≃* N)
 (K : Subgroup G) : K.map f.toMonoidHom = K.comap f.symm.toMonoidHom
-/
theorem map_equiv_eq_comap_symm (f : G ≃* N) (K : Subgroup G) :
    K.map f = K.comap (G := N) f.symm :=
  map_equiv_eq_comap_symm' _ _

@[to_additive]
/-
**Subgroup.comap_equiv_eq_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_equiv_eq_map_symm (f : N ≃* G) (K : Subgroup G) : K.comap (G
参数：f : N ≃* G；K : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : G ≃* N) (
K : Subgroup G) : K.map f = K.comap (G
-/
theorem comap_equiv_eq_map_symm (f : N ≃* G) (K : Subgroup G) :
    K.comap (G := N) f = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]
/-
**Subgroup.comap_equiv_eq_map_symm'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_equiv_eq_map_symm' (f : N ≃* G) (K : Subgroup G) : K.comap f.toMonoi
dHom = K.map f.symm.toMonoidHom
参数：f : N ≃* G；K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : G ≃* N) (
K : Subgroup G) : K.map f = K.comap (G
-/
theorem comap_equiv_eq_map_symm' (f : N ≃* G) (K : Subgroup G) :
    K.comap f.toMonoidHom = K.map f.symm.toMonoidHom :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]
/-
**Subgroup.map_symm_eq_iff_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_symm_eq_iff_map_eq {H : Subgroup N} {e : G ≃* N} : H.map ↑e.symm = K ↔
 K.map ↑e = H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_map`：map_map (g : N ->* P) (f : G ->* N) : (K.map f).map g 
= K.map (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MulEquiv.coe_monoidHom_trans`：coe_monoidHom_trans (e₁ : M ≃* N) (e₂ : N 
≃* P) : (e₁.trans e₂ : M ->* P) = (e₂ : N ->* P).comp ↑e₁
· 使用定理 `MulEquiv.symm_trans_self`：symm_trans_self (e : M ≃* N) : e.symm.trans e 
= refl N
· 使用定理 `MulEquiv.coe_monoidHom_refl`：coe_monoidHom_refl : (refl M : M ->* M) = M
onoidHom.id M
· 使用定理 `Subgroup.map_id`：map_id : K.map (MonoidHom.id G) = K
· 使用定理 `MulEquiv.self_trans_symm`：self_trans_symm (e : M ≃* N) : e.trans e.symm 
= refl M
-/
theorem map_symm_eq_iff_map_eq {H : Subgroup N} {e : G ≃* N} :
    H.map ↑e.symm = K ↔ K.map ↑e = H := by
  constructor <;> rintro rfl
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
      MulEquiv.coe_monoidHom_refl, map_id]
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
      MulEquiv.coe_monoidHom_refl, map_id]

@[to_additive]
/-
**Subgroup.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_le_iff_le_comap {f : G ->* N} {K : Subgroup G} {H : Subgroup N} : K.ma
p f <= H ↔ K <= H.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : G →* N} {K : Subgroup G} {H : Subgroup N} :
    K.map f ≤ H ↔ K ≤ H.comap f :=
  image_subset_iff

@[to_additive]
/-
**Subgroup.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：gc_map_comap (f : G ->* N) : GaloisConnection (map f) (comap f)
参数：f : G ->* N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
-/
theorem gc_map_comap (f : G →* N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

@[to_additive]
/-
**Subgroup.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_sup (H K : Subgroup G) (f : G ->* N) : (H ⊔ K).map f = H.map f ⊔ K.map
 f
参数：H K : Subgroup G；f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem map_sup (H K : Subgroup G) (f : G →* N) : (H ⊔ K).map f = H.map f ⊔ K.map f :=
  (gc_map_comap f).l_sup

@[to_additive]
/-
**Subgroup.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_iSup {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup G) : (iSup s).map f 
= ⨆ i, (s i).map f
参数：f : G ->* N；s : ι -> Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : G →* N) (s : ι → Subgroup G) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

@[to_additive]
/-
**Subgroup.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_inf (H K : Subgroup G) (f : G ->* N) (hf : Function.Injective f) : (H 
⊓ K).map f = H.map f ⊓ K.map f
参数：H K : Subgroup G；f : G ->* N；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    (H ⊓ K).map f = H.map f ⊓ K.map f := SetLike.coe_injective (Set.image_inter hf)

@[to_additive]
/-
**Subgroup.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : G ->* N) (hf : Function.Injective f
) (s : ι -> Subgroup G) : (iInf s).map f = ⨅ i, (s i).map f
参数：f : G ->* N；hf : Function.Injective f；s : ι -> Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subgroup G} : (↑(⨅ i, 
S i) : Set G) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : G →* N) (hf : Function.Injective f)
    (s : ι → Subgroup G) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]
/-
**Subgroup.comap_sup_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_sup_comap_le (H K : Subgroup N) (f : G ->* N) : comap f H ⊔ comap f 
K <= comap f (H ⊔ K)
参数：H K : Subgroup N；f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_sup`：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f
 : α -> β} (h : Monotone f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
· 使用定理 `Subgroup.comap_mono`：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <=
 K' -> comap f K <= comap f K'
-/
theorem comap_sup_comap_le (H K : Subgroup N) (f : G →* N) :
    comap f H ⊔ comap f K ≤ comap f (H ⊔ K) :=
  Monotone.le_map_sup (fun _ _ => comap_mono) H K

@[to_additive]
/-
**Subgroup.iSup_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：iSup_comap_le {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup N) : ⨆ i, (s i)
.comap f <= (iSup s).comap f
参数：f : G ->* N；s : ι -> Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_iSup`：Monotone.le_map_iSup [CompleteLattice β] {f : α ->
 β} (hf : Monotone f) : ⨆ i, f (s i) <= f (iSup s)
· 使用定理 `Subgroup.comap_mono`：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <=
 K' -> comap f K <= comap f K'
-/
theorem iSup_comap_le {ι : Sort*} (f : G →* N) (s : ι → Subgroup N) :
    ⨆ i, (s i).comap f ≤ (iSup s).comap f :=
  Monotone.le_map_iSup fun _ _ => comap_mono

@[to_additive]
/-
**Subgroup.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_inf (H K : Subgroup N) (f : G ->* N) : (H ⊓ K).comap f = H.comap f ⊓
 K.comap f
参数：H K : Subgroup N；f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem comap_inf (H K : Subgroup N) (f : G →* N) : (H ⊓ K).comap f = H.comap f ⊓ K.comap f :=
  (gc_map_comap f).u_inf

@[to_additive]
/-
**Subgroup.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_iInf {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup N) : (iInf s).coma
p f = ⨅ i, (s i).comap f
参数：f : G ->* N；s : ι -> Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem comap_iInf {ι : Sort*} (f : G →* N) (s : ι → Subgroup N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[to_additive]
/-
**Subgroup.map_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_inf_le (H K : Subgroup G) (f : G ->* N) : map f (H ⊓ K) <= map f H ⊓ m
ap f K
参数：H K : Subgroup G；f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Subgroup.map_mono`：map_mono {f : G ->* N} {K K' : Subgroup G} : K <= K' 
-> map f K <= map f K'
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem map_inf_le (H K : Subgroup G) (f : G →* N) : map f (H ⊓ K) ≤ map f H ⊓ map f K :=
  le_inf (map_mono inf_le_left) (map_mono inf_le_right)

@[to_additive]
/-
**Subgroup.map_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_inf_eq (H K : Subgroup G) (f : G ->* N) (hf : Function.Injective f) : 
map f (H ⊓ K) = map f H ⊓ map f K
参数：H K : Subgroup G；f : G ->* N；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_inf_eq (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    map f (H ⊓ K) = map f H ⊓ map f K := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

@[to_additive (attr := simp)]
/-
**Subgroup.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem map_bot (f : G →* N) : (⊥ : Subgroup G).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[to_additive]
/-
**Subgroup.disjoint_map** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：disjoint_map {f : G ->* N} (hf : Function.Injective f) {H K : Subgroup G} 
(h : Disjoint H K) : Disjoint (H.map f) (K.map f)
参数：hf : Function.Injective f；h : Disjoint H K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_inf`：map_inf (H K : Subgroup G) (f : G ->* N) (hf : Functio
n.Injective f) : (H ⊓ K).map f = H.map f ⊓ K.map f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
-/
lemma disjoint_map {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff, ← map_inf _ _ f hf, disjoint_iff.mp h, map_bot]

@[to_additive]
/-
**Subgroup.map_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_top_of_surjective (f : G ->* N) (h : Function.Surjective f) : Subgroup
.map f ⊤ = ⊤
参数：f : G ->* N；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `trivial`：True
-/
theorem map_top_of_surjective (f : G →* N) (h : Function.Surjective f) : Subgroup.map f ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, trivial, hy⟩

@[to_additive]
/-
**Subgroup.codisjoint_map** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：codisjoint_map {f : G ->* N} (hf : Function.Surjective f) {H K : Subgroup 
G} (h : Codisjoint H K) : Codisjoint (H.map f) (K.map f)
参数：hf : Function.Surjective f；h : Codisjoint H K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_sup`：map_sup (H K : Subgroup G) (f : G ->* N) : (H ⊔ K).map
 f = H.map f ⊔ K.map f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.map_top_of_surjective`：map_top_of_surjective (f : G ->* N) (h :
 Function.Surjective f) : Subgroup.map f ⊤ = ⊤
-/
lemma codisjoint_map {f : G →* N} (hf : Function.Surjective f)
    {H K : Subgroup G} (h : Codisjoint H K) : Codisjoint (H.map f) (K.map f) := by
  rw [codisjoint_iff, ← map_sup, codisjoint_iff.mp h, map_top_of_surjective _ hf]

@[to_additive (attr := simp)]
/-
**Subgroup.map_equiv_top** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：map_equiv_top {F : Type*} [EquivLike F G N] [MulEquivClass F G N] (f : F) 
: map (f : G ->* N) ⊤ = ⊤
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_top_of_surjective`：map_top_of_surjective (f : G ->* N) (h :
 Function.Surjective f) : Subgroup.map f ⊤ = ⊤
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
lemma map_equiv_top {F : Type*} [EquivLike F G N] [MulEquivClass F G N] (f : F) :
    map (f : G →* N) ⊤ = ⊤ :=
  map_top_of_surjective _ (EquivLike.surjective f)

@[to_additive (attr := simp)]
/-
**Subgroup.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f = ⊤
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem comap_top (f : G →* N) : (⊤ : Subgroup N).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`. -/
@[to_additive /-- For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`. -/]
/-
**Subgroup.subgroupOf** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf (H K : Subgroup G) : Subgroup K
参数：H K : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`.
-/
def subgroupOf (H K : Subgroup G) : Subgroup K :=
  H.comap K.subtype

/-- If `H ≤ K`, then `H` as a subgroup of `K` is isomorphic to `H`. -/
@[to_additive (attr := simps)
/-- If `H ≤ K`, then `H` as a subgroup of `K` is isomorphic to `H`. -/]
/-
**Subgroup.subgroupOfEquivOfLe** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：subgroupOfEquivOfLe {G : Type*} [Group G] {H K : Subgroup G} (h : H <= K) 
: H.subgroupOf K ≃* H where toFun g
参数：h : H <= K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subgroupOfEquivOfLe {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    H.subgroupOf K ≃* H where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨⟨g.1, h g.2⟩, g.2⟩
  map_mul' _g _h := rfl

@[to_additive]
/-
**Subgroup.subgroupOf_mono** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_mono {H₁ H₂ : Subgroup G} (H₃ : Subgroup G) (h : H₁ <= H₂) : H₁
.subgroupOf H₃ <= H₂.subgroupOf H₃
参数：H₃ : Subgroup G；h : H₁ <= H₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_mono`：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <=
 K' -> comap f K <= comap f K'
-/
lemma subgroupOf_mono {H₁ H₂ : Subgroup G} (H₃ : Subgroup G) (h : H₁ ≤ H₂) :
    H₁.subgroupOf H₃ ≤ H₂.subgroupOf H₃ :=
  comap_mono h

@[to_additive (attr := simp)]
/-
**Subgroup.comap_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_subtype (H K : Subgroup G) : H.comap K.subtype = H.subgroupOf K
参数：H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_subtype (H K : Subgroup G) : H.comap K.subtype = H.subgroupOf K :=
  rfl

@[to_additive (attr := simp)]
/-
**Subgroup.comap_inclusion_subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_inclusion_subgroupOf {K₁ K₂ : Subgroup G} (h : K₁ <= K₂) (H : Subgro
up G) : (H.subgroupOf K₂).comap (inclusion h) = H.subgroupOf K₁
参数：h : K₁ <= K₂；H : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_inclusion_subgroupOf {K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) (H : Subgroup G) :
    (H.subgroupOf K₂).comap (inclusion h) = H.subgroupOf K₁ :=
  rfl

@[to_additive]
/-
**Subgroup.coe_subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_subgroupOf (H K : Subgroup G) : (H.subgroupOf K : Set K) = K.subtype ⁻
¹' H
参数：H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subgroupOf (H K : Subgroup G) : (H.subgroupOf K : Set K) = K.subtype ⁻¹' H :=
  rfl

@[to_additive]
/-
**Subgroup.mem_subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_subgroupOf {H K : Subgroup G} {h : K} : h in H.subgroupOf K ↔ (h : G) 
in H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_subgroupOf {H K : Subgroup G} {h : K} : h ∈ H.subgroupOf K ↔ (h : G) ∈ H :=
  Iff.rfl

-- TODO(kmill): use `K ⊓ H` order for RHS to match `Subtype.image_preimage_coe`
@[to_additive (attr := simp)]
/-
**Subgroup.subgroupOf_map_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_map_subtype (H K : Subgroup G) : (H.subgroupOf K).map K.subtype
 = H ⊓ K
参数：H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem subgroupOf_map_subtype (H K : Subgroup G) : (H.subgroupOf K).map K.subtype = H ⊓ K :=
  SetLike.ext' <| by refine Subtype.image_preimage_coe _ _ |>.trans ?_; apply Set.inter_comm

@[to_additive]
/-
**Subgroup.map_subgroupOf_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_subgroupOf_eq_of_le {H K : Subgroup G} (h : H <= K) : (H.subgroupOf K)
.map K.subtype = H
参数：h : H <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.subgroupOf_map_subtype`：subgroupOf_map_subtype (H K : Subgroup 
G) : (H.subgroupOf K).map K.subtype = H ⊓ K
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
-/
theorem map_subgroupOf_eq_of_le {H K : Subgroup G} (h : H ≤ K) :
    (H.subgroupOf K).map K.subtype = H := by
  rwa [subgroupOf_map_subtype, inf_eq_left]

@[to_additive (attr := simp)]
/-
**Subgroup.bot_subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：bot_subgroupOf : (⊥ : Subgroup G).subgroupOf H = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem bot_subgroupOf : (⊥ : Subgroup G).subgroupOf H = ⊥ :=
  Eq.symm (Subgroup.ext fun _g => Subtype.ext_iff)

@[to_additive (attr := simp)]
/-
**Subgroup.top_subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：top_subgroupOf : (⊤ : Subgroup G).subgroupOf H = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_subgroupOf : (⊤ : Subgroup G).subgroupOf H = ⊤ :=
  rfl

@[to_additive]
/-
**Subgroup.subgroupOf_bot_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_bot_eq_bot : H.subgroupOf ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem subgroupOf_bot_eq_bot : H.subgroupOf ⊥ = ⊥ :=
  Subsingleton.elim _ _

@[to_additive]
/-
**Subgroup.subgroupOf_bot_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_bot_eq_top : H.subgroupOf ⊥ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem subgroupOf_bot_eq_top : H.subgroupOf ⊥ = ⊤ :=
  Subsingleton.elim _ _

@[to_additive (attr := simp)]
/-
**Subgroup.subgroupOf_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_self : H.subgroupOf H = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem subgroupOf_self : H.subgroupOf H = ⊤ :=
  top_unique fun g _hg => g.2

@[to_additive (attr := simp)]
/-
**Subgroup.subgroupOf_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_inj {H₁ H₂ K : Subgroup G} : H₁.subgroupOf K = H₂.subgroupOf K 
↔ H₁ ⊓ K = H₂ ⊓ K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem subgroupOf_inj {H₁ H₂ K : Subgroup G} :
    H₁.subgroupOf K = H₂.subgroupOf K ↔ H₁ ⊓ K = H₂ ⊓ K := by
  simpa only [SetLike.ext_iff, mem_inf, mem_subgroupOf, and_congr_left_iff] using Subtype.forall

@[to_additive (attr := simp)]
/-
**Subgroup.inf_subgroupOf_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：inf_subgroupOf_right (H K : Subgroup G) : (H ⊓ K).subgroupOf K = H.subgrou
pOf K
参数：H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.subgroupOf_inj`：subgroupOf_inj {H₁ H₂ K : Subgroup G} : H₁.subg
roupOf K = H₂.subgroupOf K ↔ H₁ ⊓ K = H₂ ⊓ K
· 使用定理 `inf_right_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ 
b ⊓ b = a ⊓ b
-/
theorem inf_subgroupOf_right (H K : Subgroup G) : (H ⊓ K).subgroupOf K = H.subgroupOf K :=
  subgroupOf_inj.2 (inf_right_idem _ _)

@[to_additive (attr := simp)]
/-
**Subgroup.inf_subgroupOf_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：inf_subgroupOf_left (H K : Subgroup G) : (K ⊓ H).subgroupOf K = H.subgroup
Of K
参数：H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Subgroup.inf_subgroupOf_right`：inf_subgroupOf_right (H K : Subgroup G) :
 (H ⊓ K).subgroupOf K = H.subgroupOf K
-/
theorem inf_subgroupOf_left (H K : Subgroup G) : (K ⊓ H).subgroupOf K = H.subgroupOf K := by
  rw [inf_comm, inf_subgroupOf_right]

@[to_additive (attr := simp)]
/-
**Subgroup.subgroupOf_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_eq_bot {H K : Subgroup G} : H.subgroupOf K = ⊥ ↔ Disjoint H K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.bot_subgroupOf`：bot_subgroupOf : (⊥ : Subgroup G).subgroupOf H 
= ⊥
· 使用定理 `Subgroup.subgroupOf_inj`：subgroupOf_inj {H₁ H₂ K : Subgroup G} : H₁.subg
roupOf K = H₂.subgroupOf K ↔ H₁ ⊓ K = H₂ ⊓ K
· 使用定理 `bot_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊓ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subgroupOf_eq_bot {H K : Subgroup G} : H.subgroupOf K = ⊥ ↔ Disjoint H K := by
  rw [disjoint_iff, ← bot_subgroupOf, subgroupOf_inj, bot_inf_eq]

@[to_additive (attr := simp)]
/-
**Subgroup.subgroupOf_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_eq_top {H K : Subgroup G} : H.subgroupOf K = ⊤ ↔ K <= H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.top_subgroupOf`：top_subgroupOf : (⊤ : Subgroup G).subgroupOf H 
= ⊤
· 使用定理 `Subgroup.subgroupOf_inj`：subgroupOf_inj {H₁ H₂ K : Subgroup G} : H₁.subg
roupOf K = H₂.subgroupOf K ↔ H₁ ⊓ K = H₂ ⊓ K
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subgroupOf_eq_top {H K : Subgroup G} : H.subgroupOf K = ⊤ ↔ K ≤ H := by
  rw [← top_subgroupOf, subgroupOf_inj, top_inf_eq, inf_eq_right]

variable (H : Subgroup G)

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsMulCommutative G] : IsMulCommutative H :=
  IsMulCommutative.of_setLike_mul_comm fun a _ b _ ↦ mul_comm' a b

@[to_additive]
/-
**Subgroup.map_isMulCommutative** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：map_isMulCommutative (f : G ->* G') [IsMulCommutative H] : IsMulCommutativ
e (H.map f)
参数：f : G ->* G'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance map_isMulCommutative (f : G →* G') [IsMulCommutative H] : IsMulCommutative (H.map f) := by
  refine .of_setLike_mul_comm ?_
  rintro - ⟨a, ha, rfl⟩ - ⟨b, hb, rfl⟩
  simpa [map_mul] using congr(f $(setLike_mul_comm ha hb))

@[to_additive]
/-
**Subgroup.comap_injective_isMulCommutative** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`
。
形式化陈述：comap_injective_isMulCommutative {f : G' ->* G} (hf : Injective f) [IsMulC
ommutative H] : IsMulCommutative (H.comap f)
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
theorem comap_injective_isMulCommutative {f : G' →* G} (hf : Injective f) [IsMulCommutative H] :
    IsMulCommutative (H.comap f) :=
  .of_setLike_mul_comm fun a (ha : f a ∈ H) b (hb : f b ∈ H) ↦ hf <| by
    simpa using setLike_mul_comm ha hb

@[to_additive]
/-
**Subgroup.subgroupOf_isMulCommutative** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_isMulCommutative [IsMulCommutative H] : IsMulCommutative (H.sub
groupOf K)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_injective_isMulCommutative`：comap_injective_isMulCommutat
ive {f : G' ->* G} (hf : Injective f) [IsMulCommutative H] : IsMulCommutative (H
.comap f)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
instance subgroupOf_isMulCommutative [IsMulCommutative H] : IsMulCommutative (H.subgroupOf K) :=
  H.comap_injective_isMulCommutative Subtype.coe_injective

end Subgroup

namespace MulEquiv
variable {H : Type*} [Group H]

set_option backward.isDefEq.respectTransparency false in
/--
An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their inverse images.

See also `MulEquiv.mapSubgroup` which maps subgroups to their forward images.
-/
@[to_additive (attr := simps)
/-- An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their inverse images.

See also `AddEquiv.mapAddSubgroup` which maps subgroups to their forward images. -/]
/-
**MulEquiv.comapSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：comapSubgroup (f : G ≃* H) : Subgroup H ≃o Subgroup G where toFun
参数：f : G ≃* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comapSubgroup (f : G ≃* H) : Subgroup H ≃o Subgroup G where
  toFun := Subgroup.comap f
  invFun := Subgroup.comap f.symm
  left_inv sg := by simp [Subgroup.comap_comap]
  right_inv sh := by simp [Subgroup.comap_comap]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.comap_comap] using
      Subgroup.comap_mono (f := (f.symm : H →* G)) h, Subgroup.comap_mono⟩

@[to_additive (attr := simp, norm_cast)]
/-
**MulEquiv.coe_comapSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：coe_comapSubgroup (e : G ≃* H) : comapSubgroup e = Subgroup.comap e.toMono
idHom
参数：e : G ≃* H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comapSubgroup (e : G ≃* H) : comapSubgroup e = Subgroup.comap e.toMonoidHom := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_comapSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：symm_comapSubgroup (e : G ≃* H) : (comapSubgroup e).symm = comapSubgroup e
.symm
参数：e : G ≃* H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_comapSubgroup (e : G ≃* H) : (comapSubgroup e).symm = comapSubgroup e.symm := rfl

set_option backward.isDefEq.respectTransparency false in
/--
An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their forward images.

See also `MulEquiv.comapSubgroup` which maps subgroups to their inverse images.
-/
@[to_additive (attr := simps)
/-- An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their forward images.

See also `AddEquiv.comapAddSubgroup` which maps subgroups to their inverse images. -/]
/-
**MulEquiv.mapSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：mapSubgroup {H : Type*} [Group H] (f : G ≃* H) : Subgroup G ≃o Subgroup H 
where toFun
参数：f : G ≃* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapSubgroup {H : Type*} [Group H] (f : G ≃* H) : Subgroup G ≃o Subgroup H where
  toFun := Subgroup.map f
  invFun := Subgroup.map f.symm
  left_inv sg := by simp [Subgroup.map_map]
  right_inv sh := by simp [Subgroup.map_map]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.map_map] using
      Subgroup.map_mono (f := (f.symm : H →* G)) h, Subgroup.map_mono⟩

@[to_additive (attr := simp, norm_cast)]
/-
**MulEquiv.coe_mapSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：coe_mapSubgroup (e : G ≃* H) : mapSubgroup e = Subgroup.map e.toMonoidHom
参数：e : G ≃* H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mapSubgroup (e : G ≃* H) : mapSubgroup e = Subgroup.map e.toMonoidHom := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_mapSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：symm_mapSubgroup (e : G ≃* H) : (mapSubgroup e).symm = mapSubgroup e.symm
参数：e : G ≃* H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mapSubgroup (e : G ≃* H) : (mapSubgroup e).symm = mapSubgroup e.symm := rfl

end MulEquiv

namespace Subgroup

open MonoidHom

variable {N : Type*} [Group N] (f : G →* N)

@[to_additive (attr := simp, norm_cast)]
/-
**Subgroup.comap_toSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：comap_toSubmonoid (e : G ≃* N) (s : Subgroup N) : (s.comap e).toSubmonoid 
= s.toSubmonoid.comap e.toMonoidHom
参数：e : G ≃* N；s : Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
lemma comap_toSubmonoid (e : G ≃* N) (s : Subgroup N) :
    (s.comap e).toSubmonoid = s.toSubmonoid.comap e.toMonoidHom := rfl

@[to_additive]
/-
**Subgroup.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_comap_le (H : Subgroup N) : map f (comap f H) <= H
参数：H : Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem map_comap_le (H : Subgroup N) : map f (comap f H) ≤ H :=
  (gc_map_comap f).l_u_le _

@[to_additive]
/-
**Subgroup.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_comap_map (H : Subgroup G) : H <= comap f (map f H)
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem le_comap_map (H : Subgroup G) : H ≤ comap f (map f H) :=
  (gc_map_comap f).le_u_l _

@[to_additive]
/-
**Subgroup.map_eq_comap_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_eq_comap_of_inverse {f : G ->* N} {g : N ->* G} (hl : Function.LeftInv
erse g f) (hr : Function.RightInverse g f) (H : Subgroup G) : map f H = comap g 
H
参数：hl : Function.LeftInverse g f；hr : Function.RightInverse g f；H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.coe_map`：coe_map (f : G ->* N) (K : Subgroup G) : (K.map f : Se
t N) = f '' K
· 使用定理 `Subgroup.coe_comap`：coe_comap (K : Subgroup N) (f : G ->* N) : (K.comap 
f : Set G) = f ⁻¹' K
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
-/
theorem map_eq_comap_of_inverse {f : G →* N} {g : N →* G} (hl : Function.LeftInverse g f)
    (hr : Function.RightInverse g f) (H : Subgroup G) : map f H = comap g H :=
  SetLike.ext' <| by rw [coe_map, coe_comap, Set.image_eq_preimage_of_inverse hl hr]

/-- A subgroup is isomorphic to its image under an injective function. If you have an isomorphism,
use `MulEquiv.subgroupMap` for better definitional equalities. -/
@[to_additive
      /-- An additive subgroup is isomorphic to its image under an injective function. If you
      have an isomorphism, use `AddEquiv.addSubgroupMap` for better definitional equalities. -/]
/-
**Subgroup.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：equivMapOfInjective (H : Subgroup G) (f : G ->* N) (hf : Function.Injectiv
e f) : H ≃* H.map f
参数：H : Subgroup G；f : G ->* N；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def equivMapOfInjective (H : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    H ≃* H.map f :=
  { Equiv.Set.image f H hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[to_additive (attr := simp)]
/-
**Subgroup.coe_equivMapOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_equivMapOfInjective_apply (H : Subgroup G) (f : G ->* N) (hf : Functio
n.Injective f) (h : H) : (equivMapOfInjective H f hf h : N) = f h
参数：H : Subgroup G；f : G ->* N；hf : Function.Injective f；h : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equivMapOfInjective_apply (H : Subgroup G) (f : G →* N) (hf : Function.Injective f)
    (h : H) : (equivMapOfInjective H f hf h : N) = f h :=
  rfl

end Subgroup

variable {N : Type*} [Group N]

namespace MonoidHom

/-- The `MonoidHom` from the preimage of a subgroup to itself. -/
@[to_additive (attr := simps!) /-- the `AddMonoidHom` from the preimage of an
additive subgroup to itself. -/]
/-
**MonoidHom.subgroupComap** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：subgroupComap (f : G ->* G') (H' : Subgroup G') : H'.comap f ->* H'
参数：f : G ->* G'；H' : Subgroup G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subgroupComap (f : G →* G') (H' : Subgroup G') : H'.comap f →* H' :=
  f.submonoidComap H'.toSubmonoid

@[to_additive]
/-
**MonoidHom.subgroupComap_surjective_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Mo
noidHom`。
形式化陈述：subgroupComap_surjective_of_surjective (f : G ->* G') (H' : Subgroup G') (
hf : Surjective f) : Surjective (f.subgroupComap H')
参数：f : G ->* G'；H' : Subgroup G'；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.submonoidComap_surjective_of_surjective`：submonoidComap_surjec
tive_of_surjective (f : M ->* N) (N' : Submonoid N) (hf : Surjective f) : Surjec
tive (f.submonoidComap N')
-/
lemma subgroupComap_surjective_of_surjective (f : G →* G') (H' : Subgroup G') (hf : Surjective f) :
    Surjective (f.subgroupComap H') :=
  f.submonoidComap_surjective_of_surjective H'.toSubmonoid hf

/-- The `MonoidHom` from a subgroup to its image. -/
@[to_additive (attr := simps!) /-- the `AddMonoidHom` from an additive subgroup to its image -/]
/-
**MonoidHom.subgroupMap** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：subgroupMap (f : G ->* G') (H : Subgroup G) : H ->* H.map f
参数：f : G ->* G'；H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MonoidHom` from a subgroup to its image.
-/
def subgroupMap (f : G →* G') (H : Subgroup G) : H →* H.map f :=
  f.submonoidMap H.toSubmonoid

@[to_additive]
/-
**MonoidHom.subgroupMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：subgroupMap_surjective (f : G ->* G') (H : Subgroup G) : Function.Surjecti
ve (f.subgroupMap H)
参数：f : G ->* G'；H : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.submonoidMap_surjective`：submonoidMap_surjective (f : M ->* N)
 (M' : Submonoid M) : Function.Surjective (f.submonoidMap M')
-/
theorem subgroupMap_surjective (f : G →* G') (H : Subgroup G) :
    Function.Surjective (f.subgroupMap H) :=
  f.submonoidMap_surjective H.toSubmonoid

end MonoidHom

namespace MulEquiv

variable {H K : Subgroup G}

/-- Makes the identity isomorphism from a proof two subgroups of a multiplicative
group are equal. -/
@[to_additive
      /-- Makes the identity additive isomorphism from a proof
      two subgroups of an additive group are equal. -/]
/-
**MulEquiv.subgroupCongr** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：subgroupCongr (h : H = K) : H ≃* K
参数：h : H = K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subgroupCongr (h : H = K) : H ≃* K :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

@[to_additive (attr := simp)]
/-
**MulEquiv.subgroupCongr_apply** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：subgroupCongr_apply (h : H = K) (x) : (MulEquiv.subgroupCongr h x : G) = x
参数：h : H = K；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subgroupCongr_apply (h : H = K) (x) :
    (MulEquiv.subgroupCongr h x : G) = x := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.subgroupCongr_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：subgroupCongr_symm_apply (h : H = K) (x) : ((MulEquiv.subgroupCongr h).sym
m x : G) = x
参数：h : H = K；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subgroupCongr_symm_apply (h : H = K) (x) :
    ((MulEquiv.subgroupCongr h).symm x : G) = x := rfl

/-- A subgroup is isomorphic to its image under an isomorphism. If you only have an injective map,
use `Subgroup.equivMapOfInjective`. -/
@[to_additive
      /-- An additive subgroup is isomorphic to its image under an isomorphism. If you only
      have an injective map, use `AddSubgroup.equivMapOfInjective`. -/]
/-
**MulEquiv.subgroupMap** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：subgroupMap (e : G ≃* G') (H : Subgroup G) : H ≃* H.map (e : G ->* G')
参数：e : G ≃* G'；H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subgroupMap (e : G ≃* G') (H : Subgroup G) : H ≃* H.map (e : G →* G') :=
  MulEquiv.submonoidMap (e : G ≃* G') H.toSubmonoid

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_subgroupMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_subgroupMap_apply (e : G ≃* G') (H : Subgroup G) (g : H) : ((subgroupM
ap e H g : H.map (e : G ->* G')) : G') = e g
参数：e : G ≃* G'；H : Subgroup G；g : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem coe_subgroupMap_apply (e : G ≃* G') (H : Subgroup G) (g : H) :
    ((subgroupMap e H g : H.map (e : G →* G')) : G') = e g :=
  rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.subgroupMap_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：subgroupMap_symm_apply (e : G ≃* G') (H : Subgroup G) (g : H.map (e : G ->
* G')) : (e.subgroupMap H).symm g = ⟨e.symm g, SetLike.mem_coe.1 Set.mem_image_e
quiv.1 g.2⟩
参数：e : G ≃* G'；H : Subgroup G；g : H.map (e : G ->* G')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem subgroupMap_symm_apply (e : G ≃* G') (H : Subgroup G) (g : H.map (e : G →* G')) :
    (e.subgroupMap H).symm g = ⟨e.symm g, SetLike.mem_coe.1 <| Set.mem_image_equiv.1 g.2⟩ :=
  rfl

end MulEquiv

namespace MonoidHom

open Subgroup

@[to_additive]
/-
**MonoidHom.closure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：closure_preimage_le (f : G ->* N) (s : Set N) : closure (f ⁻¹' s) <= (clos
ure s).comap f
参数：f : G ->* N；s : Set N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subgroup.mem_comap`：mem_comap {K : Subgroup N} {f : G ->* N} {x : G} : x
 in K.comap f ↔ f x in K
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
-/
theorem closure_preimage_le (f : G →* N) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  (closure_le _).2 fun x hx => by rw [SetLike.mem_coe, mem_comap]; exact subset_closure hx

/-- The image under a monoid homomorphism of the subgroup generated by a set equals the subgroup
generated by the image of the set. -/
@[to_additive
      /-- The image under an `AddMonoid` hom of the `AddSubgroup` generated by a set equals
      the `AddSubgroup` generated by the image of the set. -/]
/-
**MonoidHom.map_closure** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：map_closure (f : G ->* N) (s : Set G) : (closure s).map f = closure (f '' 
s)
参数：f : G ->* N；s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_comm_of_u_comm`：l_comm_of_u_comm {X : Type*} [Preorde
r X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [PartialOrder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem map_closure (f : G →* N) (s : Set G) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subgroup.gi N).gc (Subgroup.gi G).gc
    fun _ ↦ rfl

end MonoidHom

namespace Subgroup

@[to_additive]
/-
**Subgroup.surjOn_iff_le_map** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：surjOn_iff_le_map {f : G ->* N} {H : Subgroup G} {K : Subgroup N} : Set.Su
rjOn f H K ↔ K <= H.map f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma surjOn_iff_le_map {f : G →* N} {H : Subgroup G} {K : Subgroup N} :
    Set.SurjOn f H K ↔ K ≤ H.map f :=
  Iff.rfl

@[to_additive (attr := simp)]
/-
**Subgroup.equivMapOfInjective_coe_mulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`
。
形式化陈述：equivMapOfInjective_coe_mulEquiv (H : Subgroup G) (e : G ≃* G') : H.equivM
apOfInjective (e : G ->* G') (EquivLike.injective e) = e.subgroupMap H
参数：H : Subgroup G；e : G ≃* G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem equivMapOfInjective_coe_mulEquiv (H : Subgroup G) (e : G ≃* G') :
    H.equivMapOfInjective (e : G →* G') (EquivLike.injective e) = e.subgroupMap H := by
  ext
  rfl

end Subgroup

