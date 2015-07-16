.. testsetup:: *

   from pwn import *
   from capstone import CS_ARCH_X86, CS_ARCH_ARM, CS_MODE_32, CS_MODE_64, CS_MODE_ARM, CS_MODE_THUMB
   from pwnlib.rop.gadgets   import Gadget, Mem
   from pwnlib.rop.gadgetfinder import GadgetSolver, GadgetClassifier, GadgetFinder, GadgetMapper

:mod:`pwnlib.rop.rop` --- Return Oriented Programming
==========================================================

.. automodule:: pwnlib.rop.gadgetfinder
   :members:
