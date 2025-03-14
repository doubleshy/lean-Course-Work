variables (A : Type)
variables (RR : A → A → Prop)
variables (PP : A → Prop)  -- 声明 PP 是 A 上的一个谓词



theorem ex6q02 : ∀ x y : A, x = y → RR x y → RR x x :=
begin
  -- **第一步：引入变量和假设**
  assume x y,       -- 1. 让 x 和 y 是 A 的任意元素
  assume hxy,       -- 2. 假设 x = y
  assume hrxy,      -- 3. 假设 RR x y 成立

  -- **第二步：使用 `cases` 替换 `y` 为 `x`**
  cases hxy,        -- 让 `y` 在所有地方替换成 `x`
  
  -- **第三步：目标变成 `RR x x`，直接使用 `hrxy`**
  exact hrxy,       -- 直接完成证明
end







theorem ex6q04 : ∀ x y z : A, x ≠ y → (x ≠ z ∨ y ≠ z) :=
begin
  -- **第一步：引入变量和假设**
  assume x y z,  -- 让 x, y, z 是 A 中的任意元素
  assume hxy,    -- 假设 x ≠ y，即 ¬(x = y)

  -- **第二步：使用经典逻辑 (排中律) 进行分类讨论**
  cases classical.em (x = z) with hxz hxz,  -- `hxz : x = z` 或 `hxz : x ≠ z`
  
  -- **情况 1: 假设 `x = z`，需要推出 `y ≠ z`**
  right, -- 选择 `∨` 的右分支，目标是证明 `y ≠ z`
  assume hyz, -- 假设 `y = z`，尝试推导矛盾

  -- **第三步：手动推导 `x = y`**
  cases hxz,   -- 用 `hxz : x = z` 直接替换 x 为 z
  cases hyz,   -- 用 `hyz : y = z` 直接替换 y 为 z

  -- **推出矛盾**
  contradiction, -- 但 `hxy : x ≠ y`，所以 `x = y` 矛盾！

  -- **情况 2: 假设 `x ≠ z`，直接推出结论**
  left,  -- 选择 `∨` 的左分支，目标是证明 `x ≠ z`
  exact hxz, -- 直接使用 `hxz : x ≠ z`
end




variables P  : Prop

constant raa : ¬ ¬ P → P

-- 证明定理 ex6q05
theorem ex6q05 : ¬ (∀ x : A, PP x) → ∃ x : A, ¬ PP x :=
begin
  -- **第一步：假设命题的前提**
  assume h,  -- 假设 h : ¬ (∀ x, PP x)，即 "并非所有 x 都满足 PP x"

  -- **第二步：使用 raa 进行反证**
  apply raa,  -- 目标是推出 ∃ x, ¬ PP x，我们用 raa 进行反证法

  -- **第三步：假设结论不成立**
  assume h1,  -- 假设 h1 : ¬ (∃ x, ¬ PP x)，即 "所有 x 都满足 ¬¬ PP x"

  -- **第四步：尝试推出矛盾**
  apply h,    -- 目标是推出矛盾，证明 h1 不能成立

  -- **第五步：引入任意 x**
  assume x,   -- 任取 x

  -- **第六步：再次使用 raa 证明 PP x**
  apply raa,  -- 利用 ¬¬PP x → PP x
  assume h2,  -- 假设 h2 : ¬ PP x

  -- **第七步：构造矛盾**
  apply h1,   -- 这里 h1 : ¬ (∃ x, ¬ PP x)，即 "不存在满足 ¬PP x 的 x"
  existsi x,  -- 但我们构造出了一个这样的 x，使得 ¬ PP x 成立
  exact h2,   -- 这与 h1 矛盾，因此 h1 不能成立，最终推出 ∃ x, ¬ PP x
end


