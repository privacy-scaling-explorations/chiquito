from __future__ import annotations
from py_ecc import bn128
from uuid import uuid1
import json

F = bn128.FQ


def json_method(self: F):
    # Convert the integer to a byte array
    byte_array = self.n.to_bytes(32, "little")

    # Split into four 64-bit integers
    ints = [int.from_bytes(byte_array[i * 8 : i * 8 + 8], "little") for i in range(4)]

    return ints


F.__json__ = json_method


class CustomEncoder(json.JSONEncoder):
    def default(self, obj):
        if hasattr(obj, "__json__"):
            return obj.__json__()
        return super().default(obj)


# int field is the u128 version of uuid.
def uuid() -> int:
    return uuid1(node=int.from_bytes([10, 10, 10, 10, 10, 10], byteorder="little")).int
