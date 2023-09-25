from __future__ import annotations
from py_ecc import bn128
from uuid import uuid1
import json


class F(bn128.FQ):
    field_modulus = (
        21888242871839275222246405745257275088548364400416034343698204186575808495617
    )

    def __json__(self: F):
        R = 2**256
        # Convert the integer to a byte array
        montgomery_form = self.n * R % F.field_modulus
        byte_array = montgomery_form.to_bytes(32, "little")
        # Split into four 64-bit integers
        ints = [
            int.from_bytes(byte_array[i * 8 : i * 8 + 8], "little") for i in range(4)
        ]
        return ints


class CustomEncoder(json.JSONEncoder):
    def default(self, obj):
        if hasattr(obj, "__json__"):
            return obj.__json__()
        return super().default(obj)


# int field is the u128 version of uuid.
def uuid() -> int:
    return uuid1(node=int.from_bytes([10, 10, 10, 10, 10, 10], byteorder="little")).int
