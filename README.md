# pi_share

## 设计需求

业务代码首先按照多线程环境设计：需要共享所有权时使用共享指针，需要互斥或读写保护时使用锁，需要原子更新时使用原子操作；不需要同步的状态不应额外加锁。相同的业务代码也可能在**确认只有一个执行线程**的浏览器 WebAssembly 环境中运行，此时希望保留这些访问意图与常用调用形式，同时避免不必要的原子引用计数和同步开销。

本库通过构建时选择实现来满足这个需求，而不是自动根据 `wasm` 目标判断是否存在并发。默认模式使用标准库多线程原语；启用 `rc` 后改用单线程共享指针、借用检查及非原子操作。`rc` **只适用于确认不会跨线程共享这些值的构建**；支持共享内存或多线程的 WebAssembly 构建仍应使用默认模式。单线程实现不是线程安全锁或原子的替代品，不能作为 `Send + Sync` 使用。

## 构建模式

| 名称 | 默认（多线程） | `rc`（单线程） |
| --- | --- | --- |
| `Share` / `ShareWeak` | `Arc` / `sync::Weak` | `Rc` / `rc::Weak` |
| `ShareMutex` / `ShareRwLock` | `Mutex` / `RwLock` | `LockCell`（动态借用检查） |
| `SharePtr`、`ShareBool`、`ShareU8`、`ShareUsize` 等 | 标准库原子类型 | `AtomicCell`（仅单线程使用） |
| `ShareRefCell` | `ArcCell` | `XrcCell`（内部为标准库 `Rc`） |

默认不启用任何 feature。使用 `--features rc` 选择单线程实现，并自动启用 `serial`；仅启用 `serial` 只放宽 `ThreadSend` / `ThreadSync` 的标记约束，不切换上述类型。一个依赖图中的 Cargo feature 会合并，应用应为整个构建一致地选择模式。

`ShareCell` / `Cell` 始终是 `TrustCell`。单线程的 `LockCell` 遇到冲突借用会立即 panic，`try_*` 方法返回 `None`；`read` / `write` / `lock` 与多线程锁一样返回 `Result`，但不会像多线程锁一样等待，也不会中毒。单线程 `AtomicCell` 接受 `Ordering` 参数但不提供跨线程内存排序；指针、布尔值、`u8`、`usize`、`u32` 和 `u64` 有对应操作方法。尤其 `SharePtr<T>` 在默认模式存储 `*mut T`，而在 `rc` 模式直接存储 `T`；切换模式时调用方须检查构造和指针操作。不要假设不同模式下的全部方法或返回值类型完全相同。

## 借用与迁移

`ShareRefCell` 通过 `borrow()` / `borrow_mut()` 返回带生命周期的守卫；也可使用 `try_borrow()` / `try_borrow_mut()`。守卫存活期间才允许访问内部值，不再支持直接对容器进行 `Deref` / `DerefMut`。

`1.0.0` 移除了自维护的 `xrc` 模块：原先直接依赖 `pi_share::xrc` 的代码需改用标准库 `Rc` / `Weak`；依赖容器隐式解引用的代码需改为显式借用。更改前请分别在默认与 `rc` 模式下编译调用方。
