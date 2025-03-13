variables A : Type 
variables PP QQ : A → Prop  
-- 声明 A 是一个类型，PP 和 QQ 是 A 上的性质

theorem dm_pred : ¬ (∃ x : A, (PP x ∨ QQ x)) → ∀ x : A, (¬ PP x ∧ ¬ QQ x) :=
begin
  assume h x,    -- 假设 h : ¬ (∃ x : A, (PP x ∨ QQ x))，并取任意 x : A
  constructor,   -- 目标是证明 ¬ PP x ∧ ¬ QQ x，使用 constructor 拆成两部分

  -- 证明 ¬ PP x
  assume hp,     -- 假设 PP x 为真
  apply h,       -- 试图利用 h : ¬∃ x : A, (PP x ∨ QQ x) 导出矛盾
  constructor,   -- 构造 ∃ x : A, (PP x ∨ QQ x)
  left,          -- 选择 ∨ 的左侧，即 PP x
  exact hp,      -- 直接使用假设 PP x

  -- 证明 ¬ QQ x
  assume hq,     -- 假设 QQ x 为真
  apply h,       -- 试图利用 h : ¬∃ x : A, (PP x ∨ QQ x) 导出矛盾
  constructor,   -- 构造 ∃ x : A, (PP x ∨ QQ x)
  right,         -- 选择 ∨ 的右侧，即 QQ x
  exact hq,      -- 直接使用假设 QQ x
end
