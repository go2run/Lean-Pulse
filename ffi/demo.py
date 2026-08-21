import ctypes, sys
lib = ctypes.CDLL(sys.argv[1], mode=ctypes.RTLD_GLOBAL)

lib.lean_initialize_runtime_module()
LEAN_IO_WORLD = ctypes.c_void_p(1)          # lean_box(0)
lib.initialize_VelvetFFI.argtypes = [ctypes.c_uint8, ctypes.c_void_p]
lib.initialize_VelvetFFI.restype = ctypes.c_void_p
lib.initialize_VelvetFFI(1, LEAN_IO_WORLD)
lib.lean_io_mark_end_initialization()

lib.velvet_maximum.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
lib.velvet_maximum.restype = ctypes.c_uint64
for a, b in [(3, 7), (42, 17), (5, 5)]:
    print(f"velvet_maximum({a}, {b}) = {lib.velvet_maximum(a, b)}")
