from __future__ import annotations

from chiquito.expr import Expr

# Commented out to avoid circular reference
# from chiquito_ast import InternalSignal, ForwardSignal, SharedSignal, FixedSignal, ASTStepType


# pub enum Queriable<F> {
#     Internal(InternalSignal),
#     Forward(ForwardSignal, bool),
#     Shared(SharedSignal, i32),
#     Fixed(FixedSignal, i32),
#     StepTypeNext(ASTStepTypeHandler),
#     Halo2AdviceQuery(ImportedHalo2Advice, i32),
#     Halo2FixedQuery(ImportedHalo2Fixed, i32),
#     #[allow(non_camel_case_types)]
#     _unaccessible(PhantomData<F>),
# }


class Queriable(Expr):
    # __hash__ method is required, because Queriable is used as a key in the assignment dictionary.
    def __hash__(self: Queriable):
        return hash(self.uuid())

    # Implemented in all children classes, and only children instances will ever be created for Queriable.
    def uuid(self: Queriable) -> int:
        pass


# Not defined as @dataclass, because inherited __hash__ will be set to None.
class Internal(Queriable):
    def __init__(self: Internal, signal: InternalSignal):
        self.signal = signal

    def uuid(self: Internal) -> int:
        return self.signal.id

    def __str__(self: Internal) -> str:
        return self.signal.annotation

    def __json__(self):
        return {"Internal": self.signal.__json__()}


class Forward(Queriable):
    def __init__(self: Forward, signal: ForwardSignal, rotation: bool):
        self.signal = signal
        self.rotation = rotation

    def next(self: Forward) -> Forward:
        if self.rotation:
            raise ValueError("Cannot rotate Forward twice.")
        else:
            return Forward(self.signal, True)

    def uuid(self: Forward) -> int:
        return self.signal.id

    def __str__(self: Forward) -> str:
        if not self.rotation:
            return self.signal.annotation
        else:
            return f"next({self.signal.annotation})"

    def __json__(self):
        return {"Forward": [self.signal.__json__(), self.rotation]}


class Shared(Queriable):
    def __init__(self: Shared, signal: SharedSignal, rotation: int):
        self.signal = signal
        self.rotation = rotation

    def next(self: Shared) -> Shared:
        return Shared(self.signal, self.rotation + 1)

    def prev(self: Shared) -> Shared:
        return Shared(self.signal, self.rotation - 1)

    def rot(self: Shared, rotation: int) -> Shared:
        return Shared(self.signal, self.rotation + rotation)

    def uuid(self: Shared) -> int:
        return self.signal.id

    def __str__(self: Shared) -> str:
        if self.rotation == 0:
            return self.signal.annotation
        else:
            return f"{self.signal.annotation}(rot {self.rotation})"

    def __json__(self):
        return {"Shared": [self.signal.__json__(), self.rotation]}


class Fixed(Queriable):
    def __init__(self: Fixed, signal: FixedSignal, rotation: int):
        self.signal = signal
        self.rotation = rotation

    def next(self: Fixed) -> Fixed:
        return Fixed(self.signal, self.rotation + 1)

    def prev(self: Fixed) -> Fixed:
        return Fixed(self.signal, self.rotation - 1)

    def rot(self: Fixed, rotation: int) -> Fixed:
        return Fixed(self.signal, self.rotation + rotation)

    def uuid(self: Fixed) -> int:
        return self.signal.id

    def __str__(self: Fixed) -> str:
        if self.rotation == 0:
            return self.signal.annotation
        else:
            return f"{self.signal.annotation}(rot {self.rotation})"

    def __json__(self):
        return {"Fixed": [self.signal.__json__(), self.rotation]}


class StepTypeNext(Queriable):
    def __init__(self: StepTypeNext, step_type: ASTStepType):
        self.step_type = step_type

    def uuid(self: ASTStepType) -> int:
        return self.id

    def __str__(self: ASTStepType) -> str:
        return self.name

    def __json__(self):
        return {
            "StepTypeNext": {"id": self.step_type.id, "annotation": self.step_type.name}
        }
