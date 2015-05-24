#!/usr/bin/env python2
# -*- coding:utf-8 -*-

import os
import re
import sys
import time
import struct
import capstone
import hashlib
import tempfile
import collections

from .elf     import ELF
from .util    import packing
from .log     import getLogger

from multiprocessing    import Pool
from itertools          import repeat
from operator           import itemgetter
from copy               import deepcopy

from barf.barf import BARF
from barf.arch import arch
from barf.analysis.gadget import RawGadget
from barf.analysis.gadget.gadgetfinder import GadgetTreeNode
from barf.analysis.gadget.gadgetverifier import GadgetVerifier
from barf.core.reil import ReilMnemonic
from barf.core.reil import ReilRegisterOperand
from barf.core.reil import ReilEmptyOperand
from barf.core.reil import ReilImmediateOperand
from barf.core.reil import DualInstruction

from barf.arch.x86.x86parser import X86Parser
from barf.arch.x86.x86translator import FULL_TRANSLATION
from barf.arch.x86.x86translator import LITE_TRANSLATION

log = getLogger(__name__)

# File size more than 100kb, should be filter for performance trade off
MAX_SIZE = 100

class VerifyROP(GadgetVerifier):

    def __init__(self, code_analyzer, architecture_info, binary_arch):
        # Simulate a stack.
        self.STACK_MAX_LEN = 1024
        self.arch = binary_arch
        super(VerifyROP, self).__init__(code_analyzer, architecture_info)

    def _verify_paths(self, paths):
        result = []
        for path in paths:
            res = self._verify_path(path, cond=[])
            if res:
                result.append(res)

        return result

    def _verify_path(self, path, cond=[]):
        """Solve the stack of a gadget path.
        """
        
        self.analyzer.reset(full=True)
        for gadget in path:
            for reil_instr in gadget.get_ir_instrs():
                if reil_instr.mnemonic == ReilMnemonic.RET:
                    break
                self.analyzer.add_instruction(reil_instr)

        dst = set()
        for i in path[-1].destination:
            if isinstance(i, ReilRegisterOperand):
                dst.add(i.name)

        sat, rsp, stack_result = False, 0, []
        if self.arch == arch.ARCH_X86:
            if self._arch_info.architecture_mode == arch.ARCH_X86_MODE_64:
                sat, rsp, stack_result = self._satisfy_x64(cond)
            elif self._arch_info.architecture_mode == arch.ARCH_X86_MODE_32:
                sat, rsp, stack_result = self._satisfy_x86(cond)
        elif self.arch == arch.ARCH_ARM:
            if self._arch_info.architecture_mode == arch.ARCH_ARM_MODE_32:
                sat, rsp, stack_result = self._satisfy_arm(cond)

        if sat:
            return (path, rsp, stack_result)
        else:
            return None


    def _satisfy_arm(self, cond):

        r = {}
        flag = False
        if len(cond) > 0:
            for (reg, value) in cond:
                if reg == "r13" or reg == "sp":
                    flag = True
                r[reg] = self.analyzer.get_register_expr(reg, mode="post")
                self.analyzer.set_postcondition(r[reg] == value)

        if not flag:
            # TODO: how about jump to another buffer, like leave; ret in x86
            pass

        sp_pre = self.analyzer.get_register_expr("sp", mode="pre")
        sp_post = self.analyzer.get_register_expr("sp", mode="post")
        self.analyzer.set_precondition(sp_pre == 0)

        stack = []
        for i in xrange(self.STACK_MAX_LEN):
            stack.append(self.analyzer.get_memory_expr(sp_pre + i*4, 4))

        stack_result = []
        if self.analyzer.check() == 'sat':
            sp_val = self.analyzer.get_expr_value(sp_post)

            for i in xrange((sp_val/4 - 1)):
                t = self.analyzer.get_expr_value(stack[i])
                stack_result.append((i, t))

            return (True, sp_val, stack_result)
        else:
            return (False, 0, [])

    def _satisfy_x64(self, cond):
       
        r = {}
        flag = False
        if len(cond) > 0:
            for (reg, value) in cond:
                if reg == "rsp":
                    flag = True
                r[reg] = self.analyzer.get_register_expr(reg, mode="post")
                self.analyzer.set_postcondition(r[reg] == value)

        # if rsp not be specified, rbp shoud not be modified. 
        if not flag:
            rbp_pre = self.analyzer.get_register_expr("rbp", mode="pre")
            rbp_con = self.analyzer.get_memory_expr(rbp_pre, 8)

            rbp_post = self.analyzer.get_register_expr("rbp", mode="post")
            self.analyzer.set_postcondition(rbp_post != rbp_con)

        rsp_pre = self.analyzer.get_register_expr("rsp", mode="pre")
        rsp_post = self.analyzer.get_register_expr("rsp", mode="post")
        self.analyzer.set_precondition(rsp_pre == 0)

        stack = []
        for i in xrange(self.STACK_MAX_LEN):
            stack.append(self.analyzer.get_memory_expr(rsp_pre + i*8, 8))


        stack_result = []
        if self.analyzer.check() == 'sat':

            rsp_val = self.analyzer.get_expr_value(rsp_post)

            for i in xrange((rsp_val/8) - 1):
                t = self.analyzer.get_expr_value(stack[i])
                stack_result.append((i, t))

            return (True, rsp_val, stack_result)
        else:
            return (False, 0, [])

    def _satisfy_x86(self, cond):

        r = {}
        flag = False
        if len(cond) > 0:
            for (reg, value) in cond:
                if reg == "esp":
                    flag = True
                r[reg] = self.analyzer.get_register_expr(reg, mode="post")
                self.analyzer.set_postcondition(r[reg] == value)

        # if esp not be specified, ebp shoud not be modified. 
        if not flag:
            ebp_pre = self.analyzer.get_register_expr("ebp", mode="pre")
            ebp_con = self.analyzer.get_memory_expr(ebp_pre, 4)

            ebp_post = self.analyzer.get_register_expr("ebp", mode="post")
            self.analyzer.set_postcondition(ebp_post != ebp_con)

        esp_pre = self.analyzer.get_register_expr("esp", mode="pre")
        esp_post = self.analyzer.get_register_expr("esp", mode="post")
        self.analyzer.set_precondition(esp_pre == 0)

        stack = []
        for i in xrange(self.STACK_MAX_LEN):
            stack.append(self.analyzer.get_memory_expr(esp_pre + i*4, 4))

        stack_result = []
        if self.analyzer.check() == "sat":
            esp_val = self.analyzer.get_expr_value(esp_post)

            for i in xrange((esp_val/4) - 1):
                t = self.analyzer.get_expr_value(stack[i])
                stack_result.append((i, t))

            return (True, esp_val, stack_result)
        else:
            return (False, 0, [])

class ROP():

    def __init__(self, elfs, base = None, byte_depth=20, instrs_depth=7):
        

        if isinstance(elfs, ELF):
            filename = elfs.file.name
            elfs = [elfs]
        elif isinstance(elfs, (str, unicode)):
            filename = elfs
            elfs = [ELF(elfs)]
        elif isinstance(elfs, (tuple, list)):
            filename = elfs[0].file.name
        else:
            log.error("ROP: Cannot load such elfs.")

        self.elfs  = elfs
        self.bin = BARF(filename)
        self.elf = elfs[0]

        self.align = max(e.elfclass for e in elfs)/8
        self.base = base
        self.migrated = False
        self.depth = 10
        self._ir_trans = self.bin.ir_translator
        self._parser = self.bin.disassembler._parser
        self.verifier = VerifyROP(self.bin.code_analyzer, self.bin.arch_info, self.bin.binary.architecture)

        #find gadgets.
        self.candidates = None

        self.need_filter = False
        if self.bin.binary.architecture == arch.ARCH_X86 and len(self.elf.file.read()) >= MAX_SIZE*1000:
            self.need_filter = True

        if self.bin.binary.architecture == arch.ARCH_X86:
            self.arch = capstone.CS_ARCH_X86
            if self.bin.binary.architecture_mode == arch.ARCH_X86_MODE_64:
                self.mode = capstone.CS_MODE_64
            elif self.bin.binary.architecture_mode == arch.ARCH_X86_MODE_32:
                self.need_filter = True
                self.mode = capstone.CS_MODE_32
            gadgets = self.__load_x86_gadgets()
            self.__convert_to_REIL(gadgets)
        elif self.bin.binary.architecture == arch.ARCH_ARM:
            self.arch = capstone.CS_ARCH_ARM
            gadgets = self.__load_arm_gadgets()
            self.__convert_to_REIL(gadgets)
        
        #classified the gadgets
        self.classified = self.do_classify()
        
        #verify the gadgets
        self.verified = self.do_verify()


        self._chain = []
        self._gadget_graph = {}
        self.__build_graph()
       
        self._global_delete_gadget = {}
        gadget_graph = deepcopy(self._gadget_graph)

        self._top_sorted = self.__build_top_sort(gadget_graph)
        # Delete  circles in graph
        for d, dlist in self._global_delete_gadget.items():
            for i in dlist:
                # TODO: Fix this bug
                self._gadget_graph[d].remove(i)

    def __filter_for_big_binary_or_elf32(self, gadgets):
        '''Filter gadgets for big binary.
        '''
        new = []
        pop   = re.compile(r'^pop (.{3})')
        add   = re.compile(r'^add .sp, (\S+)$')
        ret   = re.compile(r'^ret$')
        leave = re.compile(r'^leave$')
        mov   = re.compile(r'^mov (.{3}), (.{3})')
        xchg  = re.compile(r'^xchg (.{3}), (.{3})')

        valid = lambda insn: any(map(lambda pattern: pattern.match(insn), [pop,add,ret,leave,mov,xchg]))

        insns = [g.strip() for g in gadgets["gadget"].split(";")]
        if all(map(valid, insns)):
            new.append(gadgets)

        return new


    def for_debug_graph(self):
        for g, list in self._gadget_graph.items():
            print str(g), "\t", "; ".join([str(dinstr.asm_instr) for dinstr in g.instrs])
            for x in list:
                print "\t", str(x), "\t", "; ".join([str(dinstr.asm_instr) for dinstr in x.instrs])

    def for_debug_v(self):
        '''For debug verified gadgets.
        '''
        for x in self.verified:
            print hex(x.address), str(x), \
                    "; ".join([str(dinstr.asm_instr) for dinstr in x.instrs])#, \
        print len(self.verified)
            

    def for_debug_c(self):
        '''For debug classified gadgets.
        '''
        for x in self.classified:
            print hex(x.address), str(x), \
                    "; ".join([str(dinstr.asm_instr) for dinstr in x.instrs]), \
                    " +++++ssss: ",\
                    " / ".join(str(one) for one in x.sources),\
                    " +++++dddd: ",\
                    " / ".join(str(one) for one in x.destination)


    def for_debug_d(self):
        '''For debug raw gadgets.
        '''
        print len(self.candidates)
        for x in self.candidates:
            print hex(x.address), "; ".join([str(dinstr.asm_instr) for dinstr in x.instrs])

    def filter_duplicates(self):
        '''Deduplicate gadgets.
        Source from BARF project.
        '''
        gadgets = {}
        for cand in self.candidates:
            asm_instrs = " ; ".join([str(dinstr.asm_instr) for dinstr in cand.instrs])

            if asm_instrs not in gadgets:
                gadgets[asm_instrs] = cand

        return [cand for asm_instrs, cand in gadgets.items()]

    def do_classify(self):
        '''Classify gadgets, using REIL emulator.
        '''

        classified = []

        for gadget in self.candidates:
            classified += self.bin.gadget_classifier.classify(gadget)

        return classified

    def do_verify(self):
        '''Verify gadgets, using Code_Analyzer module of BARF.
        '''
        verified = []

        for gadget in self.classified:

            # TODO: filter only ret instructions
            #if gadget.get_ir_instrs()[-1].mnemonic != ReilMnemonic.RET:
                #continue

            valid = self.bin.gadget_verifier.verify(gadget)
            
            if valid:
                gadget.is_valid = True
                verified += [gadget]

        return verified

    def call(self, resolvable, arguments=()):
        '''Add a function to rop chain.
        '''

        addr = self.resolve(resolvable)

        if addr is None:
            log.error("Could not resolve %r" % resolvable)

        self._chain.append((addr, arguments))
    
    def raw(self, value):
        """Adds a raw integer or string to the ROP chain.

        If your architecture requires aligned values, then make
        sure that any given string is aligned!

        Arguments:
            data(int/str): The raw value to put onto the rop chain.
        """

        if self.migrated:
            log.error("Cannot append to a migrated chain")

        self._chain.append((value, ()))

    def _output_struct(self, value, output):
        next_index = len(output)

        if isinstance(value, (int, long)):
            return value
        elif isinstance(value, (unicode, str)):
            if isinstance(value, unicode):
                value = value.encode('utf8')

            while True:
                value += '\x00'
                if len(value) % self.align == 0:
                    break

            output.append([value])
            return (next_index,)
        elif isinstance(value, (tuple, list)):
            l = []
            output.append(l)
            for v in value:
                l.append(self._output_struct(v, output))
            return (next_index,)
        else:
            log.error("ROP: Cannot flatten value %r" % value)

    def __find_suitable_gadget(self, gg, arglen):
        '''Find gadgets, which esp jump just >= argument_length*4 + 4(ret) 
        '''
        for g, jump, _ in gg:
            if jump >= arglen*4 + 4:
                return (True, g, jump)

        print "Cannot find out one suitable gadget."
        return (False, 0, 0)

    def build(self, base=None):
        '''Automatic build rop chain for binary.
        '''

        if base == None:
            base = self.base

        out = []
        meth = '_build_' + self.elfs[0].get_machine_arch()
        if not hasattr(self, meth):
            log.error("Cannot build rop for architecture %r" % self.elfs[0].get_machine_arch())
        rop = getattr(self, meth)()

        addrs = {}
        if base != None:
            addr = base
            for i, l in enumerate(rop):
                addrs[i] = addr
                for v in l:
                    if isinstance(v, (int, long, tuple)):
                        addr += self.align
                    else:
                        addr += len(v)

        addr = base or 0
        out = []
        for l in rop:
            for v in l:
                if isinstance(v, (int, long)):
                    out.append((addr, v, False))
                    addr += self.align
                elif isinstance(v, str):
                    out.append((addr, v, False))
                    addr += len(v)
                elif isinstance(v, tuple):
                    if v[0] in addrs:
                        out.append((addr, addrs[v[0]], True))
                        addr += self.align
                    elif base != None:
                        log.error("ROP: References unknown structure index")
                    else:
                        log.error("ROP: Cannot use structures without a base address")
                else:
                    log.error("ROP: Unexpected value: %r" % v)

        return out

    def chain(self):
        """Build the ROP chain

        Returns:
            str containging raw ROP bytes
        """

        return packing.flat(
            [value for addr, value, was_ref in self.build()],
            word_size = 8*self.align
        )

    def dump(self):
        """Dump the ROP chain in an easy-to-read manner"""
        result = []

        rop = self.build(self.base or 0)
        addrs = [addr for addr, value, was_ref in rop]
        for addr, value, was_ref in rop:
            if isinstance(value, str):
                line   = "0x%04x: %16r" % (addr, value.rstrip('\x00'))
            elif isinstance(value, (int, long)):
                if was_ref:
                    line = "0x%04x: %#16x (%+d)" % (
                        addr,
                        value,
                        value - addr
                    )
                else:
                    ref = self.unresolve(value)
                    line = "0x%04x: %#16x%s" % (
                        addr,
                        value,
                        (' (%s)' % ref) if ref else ''
                    )
            else:
                log.error("ROP: ROP.build returned an unexpected value %r" % value)

            result.append(line)

        return '\n'.join(result)

    def __build_x86(self):
        '''Build rop chain for elf x86.
        '''
        outrop = []
        output = [outrop]

        gg = self.verifier._verify_paths(self.__find_x86_paths())
        gg = sorted(gg, key=itemgetter(1))

        for index, (addr, arguments)  in enumerate(self._chain):
            if not arguments:
                outrop.append(addr)

            else:
                outrop.append(addr)

                if not isinstance(arguments, tuple):
                    arguments = (arguments,)
                arglen = len(arguments)
                
                r, g, jump = self.__find_suitable_gadget(gg, arglen)
                if r:
                    compensation = jump - arglen*4 - 4
                    outrop.append(g[0].address)

                    for arg in arguments:
                        outrop.append(self._output_struct(arg, output))

                    for _ in range(compensation/4):
                        outrop.append('$$$$')

        return output


    _build_i386 = __build_x86

    def __build_x64(self):
        '''Build rop chain for elf x86.
        '''
        outrop = []
        output = [outrop]

        # The number of Arguments more than 6 ! Are you crazy?
        # For GCC now, TODO: windows & mach
        regs = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]

        for index, (addr, arguments) in enumerate(self._chain):
            if not arguments:
                outrop.append(addr)

            else:
                if not isinstance(arguments, tuple):
                    arguments = (arguments,)

                input_values = dict(zip(regs, arguments))
                stack = self.set_registers(input_values)
                stack_concate = reduce(lambda x, y: x + y, stack.values())
                outrop += stack_concate

                outrop.append(addr)

        return output 

    _build_amd64 = __build_x64


    def __build_arm(self):
        outrop = []
        output = [outrop]

        regs = ["r0", "r1", "r2", "r3", "r4", "r5"]

        for index, (addr, arguments) in enumerate(self._chain):
            if not arguments:
                outrop.append(addr)

            else:
                if not isinstance(arguments, tuple):
                    arguments = (arguments,)

                input_values = dict(zip(regs, arguments))
                stack = self.set_registers(input_values)
                stack_concate = reduce(lambda x, y: x + y, stack.values())
                outrop += stack_concate

                outrop.append(addr)

        return output

    _build_arm = __build_arm


    def resolve(self, resolvable):
        """Resolves a symbol to an address

        Arguments:
            resolvable(str,int): Thing to convert into an address

        Returns:
            int containing address of 'resolvable', or None
        """
        if isinstance(resolvable, str):
            if resolvable in self.elf.symbols:
                return self.elf.symbols[resolvable]
        if isinstance(resolvable, (int,long)):
            return resolvable
        return None

    def unresolve(self, value):
        """Inverts 'resolve'.  Given an address, it attempts to find a symbol
        for it in the loaded ELF files.  If none is found, it searches all
        known gadgets, and returns the disassembly

        Arguments:
            value(int): Address to look up

        Returns:
            String containing the symbol name for the address, disassembly for a gadget
            (if there's one at that address), or an empty string.
        """
        for elf in self.elfs:
            for name, addr in elf.symbols.items():
                if addr == value:
                    return name

        for gad in self.classified:
            if value == gad.address:
                return "; ".join([str(dinstr.asm_instr) for dinstr in gad.instrs])

        return ''

    def __build_graph(self):
        '''Build gadgets graph, gadget as vertex, reg as edge.
        '''
        for instr in self.verified:
            #inital gadgets graph
            self._gadget_graph[instr] = set()

            regmaps = self.bin.arch_info.alias_mapper
            regall = self.bin.arch_info.registers_size
            op_size = self.bin.arch_info.operand_size

            g_str1, _ = str(instr).split(" > ")
            lhand1, _ = g_str1.split(" <- ")
            dst_reg = lhand1
            
            if dst_reg.startswith("mem"):
                continue

            for reg, size in regall.items():
                if reg == dst_reg and size != op_size:
                    dst_reg = regmaps[dst_reg][0]

            for instr_b in self.verified:
                if instr == instr_b:
                    continue
                
                g_str2, _ = str(instr_b).split(" > ")
                _ , rhand2 = g_str2.split(" <- ")
                src_reg = rhand2
                
                if src_reg.startswith("0x"):
                    continue
                if src_reg.startswith("mem"):
                    continue

                # TODO: regs for arithmetic operations
                if len(src_reg) > 3:
                    continue
                
                for reg, size in regall.items():
                    if reg == src_reg and size != op_size:
                        src_reg = regmaps[src_reg][0]

                if dst_reg == src_reg:
                    self._gadget_graph[instr].add(instr_b)

    def __build_top_sort(self, graph):
        """
        Topological sort a graph.

        Arguments:
            
            graph(dict):
                A simple example : graph = {'eax': ['ebx'], 'ebx': ['eax'], 'edx': ['eax']}
                May be cycles in graph. we need to handle it.

        Return Value:
            top_sorted(list):
                such as: ["edx", "eax", "ebx"]
        """
        top_sorted = []
        indegree_zero = []

        #Inital indegree list will zero.
        indegree = {}
        for k, v in graph.items():
            indegree[k] = 0
            for l in v:
                indegree[l] = 0

        #Caculate indegree, for gadget graph.
        for g, glist in graph.items():
            for gadget in glist:
                indegree[gadget] += 1
        
        #inital indegree_zero list.
        for g, indeg in indegree.items():
            if indeg == 0:
                indegree_zero.append(g)

        # TOP sort
        while len(indegree_zero) > 0:
            n = indegree_zero.pop()
            top_sorted.append(n)

            if n not in graph.keys():
                continue

            for m in graph[n]:
                indegree[m] -= 1
                if indegree[m] == 0:
                    indegree_zero.append(m)
            del(graph[n])
       
        if len(graph) == 0:
            return top_sorted

        # Recursive top sort.
        for g, indeg in indegree.items():
            if indeg == 1:
                for k, glist in graph.items():
                    for h in glist:
                        if h == g:
                            #delete the edge of a cirle.
                            graph[k].remove(h)

                            #record the deleted edge of cirles.
                            if k not in self._global_delete_gadget.keys():
                                self._global_delete_gadget[k] = set()
                            self._global_delete_gadget[k].add(h)
                            
                            # Recurisve top sorting.
                            last_result = self.__build_top_sort(graph)

                            return top_sorted + last_result


    def set_registers(self, values):
        """
        Provides a sequence of ROP gadgets which will set the desired register
        values.

        Arguments:

            values(dict):
                Mapping of ``{register name: value}``.  The contents of
                ``value`` can be any object, not just an integer.

        Return Value:

            Returns a ``collections.OrderedDict`` object which is in the
            correct order of operations.

            The keys are the register names, and the values are the sequence
            of stack values necessary to set the register.

        Example:

            Assume we have the following gadgets.

            1000: pop eax; ret
            2000: mov ebx, eax; ret
            3000: pop ecx; ret
            4000: mov edx, ebx; ret

            For simple cases, the order doesn't matter.
            (Note: The display for OrderedDict is ugly, sorry!)

            >>> set_registers({'eax': 1})
            OrderedDict([('eax', [1000, 1])])
            OrderedDict([('eax', [1000], 8, [(0, 1)])])
            >>> set_registers({'eax': 1, 'ecx': 0})
            OrderedDict([('eax', [1000, 1]), ('ecx', [3000, 0])])
            >>> set_registers({'ebx': None})
            OrderedDict([('ebx', [1000, None, 2000])])

            For complex cases, there is only one possible ordering:

            >>> set_registers({'eax': 1, 'ebx': None})
            OrderedDict([('ebx', [1000, None, 2000]), ('eax', [1000, 1])])

            Sometimes, it may not be possible/

            >>> set_registers({'esi': 0})
            <exception>
        """
        out = []
        ropgadgets = {}
        gadget_list = {}

        if isinstance(values, list):
            values = dict(values)

        regmaps = self.bin.arch_info.alias_mapper
        for reg, value in values.items():

            ropgadget = self.search(regmaps["sp"][0], [reg])[0]
            if not ropgadget:
                log.error("Gadget to reg %s not found!" % reg)

            # Combine the same gadgets together.
            last_gadget_address = ropgadget[-1].address
            ropgadgets[last_gadget_address] = ropgadget
            if last_gadget_address not in gadget_list.keys():
                gadget_list[last_gadget_address] = []
            gadget_list[last_gadget_address].append(reg)

        for address, regs in gadget_list.items():
            ropgadget = ropgadgets[address]
            conditions = []
            for reg in regs:
                conditions += [(reg, values[reg])]
            path, sp, stack = self.__verify_path(ropgadget, conditions)
            out += [("_".join(regs), (ropgadget, sp, stack))]

        ordered_out = collections.OrderedDict(sorted(out, 
                      key=lambda t: self._top_sorted[::-1].index(t[1][0][-1])))

        ordered_out = self.flat_as_stack(ordered_out)

        return ordered_out
    
    def flat_as_stack(self, ordered_dict):
        
        out = []
        junk = "$" * self.align

        for reg, result in ordered_dict.items():
            outrop = []
            ropgadget, _, _ = result
            sp = 0
            know = {}
            for gad in ropgadget:
                if sp != 0:
                    know[sp / self.align] = gad.address
                temp_result = self.__verify_path([gad])
                sp += temp_result[1]

            ropgadget, _, stack_result = result
            outrop.append(ropgadget[0].address)

            for pos, value in stack_result:
                if pos in know.keys():
                    outrop.append(know[pos])
                    continue
                if value == 0:
                    value = junk

                outrop.append(value)
            out += [(reg, outrop)]

        out = collections.OrderedDict(out)
        return out


    def solve_register_dependencies(self, registers, values):
        """
        Provides register move ordering.

        Arguments:
            registers: List of possible registers (e.g. ['eax','ebx',...]
            values: Dictionary which maps registers to their desired values.

            In some architectures, dependency cycles can be solved with an
            'exchange' instruction (e.g. ``xchg eax, esp``).

            To handle this circumstance, a ``tuple`` should be returned
            which contains the two registers.

        Returns:
            Order in which registers should be set in order to avoid conflicts.

        Example:

            In this example, 'ebx' must be set before 'eax', since 'ebx'
            requires the current value in 'eax'.

            >>> want = {'eax': 11, 'ebx': 'eax', 'ecx': 'esi', 'edx': 'edx'}
            >>> all  = ['eax', 'ebx', 'ecx', 'edx', 'esi']
            >>> solve_register_dependencies(all, want)
            ['ebx', 'eax', 'esi']

            This example demonstrates a dependency cycle.

            >>> want = {'eax': 'ebx', 'ebx': 'eax'}
            >>> solve_register_dependencies(all, want)
            [('eax','ebx')]
        """

        # Build graph
        # Consider multi to multi dependency relationship
        reg_graph = {}
        for k, v in values.items():
            if not isinstance(v, list):
                v = [v]
            reg_graph[k] = v

        # Top sort
        all_tuple = []
        reg_graph2 = deepcopy(reg_graph)
        self._global_delete_gadget = {}
        top_sorted = self.__build_top_sort(reg_graph2)
        
        # look for cycles
        for reg, regs_list in self._global_delete_gadget.items():
            for one in regs_list:
                if reg in reg_graph[one]:
                    all_tuple += [(one, reg)]
        
        all_cycle_regs = dict(all_tuple)

        registers = list(set(registers) & set(top_sorted) - set(all_cycle_regs.values()))
        ordered_out = sorted(registers, key=lambda t: top_sorted.index(t))

        for i in range(len(ordered_out)):
            one = ordered_out[i]
            if one in all_cycle_regs.keys():
                ordered_out[i] = (one, all_cycle_regs[one])

        return ordered_out


    def __find_x86_paths(self):
        '''Search paths for ELF32, now only support single instruction arrangement.
        TODO: two more gadgets arrangement support.
        '''
        asm_instr_dict = {}

        #deduplicate gadgets with same instruction
        for instr in self.verified:
            asm_instr = "; ".join([str(dinstr.asm_instr) for dinstr in instr.instrs])
            asm_instr_dict[asm_instr] = instr

        return [ [instr] for _, instr in asm_instr_dict.items()]

    def search(self, src, regs):
        '''Search paths, from src to regs.
        Example: search("rsp", ["rdi"]), such as gadget "pop rdi; ret" will be return to us.
        '''
        start = set()
        for instr in self.verified:
            instr_srcs = [str(s) for s in instr.sources]
            if src in instr_srcs:
                start.add(instr)

        end = set()

        alldst = {}
        for reg in regs:
            alldst[reg] = set()

        asm_instr_dict = {}
        for instr in self.verified:
            asm_instr = "; ".join([str(dinstr.asm_instr) for dinstr in instr.instrs])
            asm_instr_dict[asm_instr] = instr
            instr_dsts = [str(s) for s in instr.destination]
            for reg in regs:
                if reg in instr_dsts:
                    alldst[reg].add(asm_instr)

        dstlist = [v for k, v in alldst.items()]
        results = reduce(set.intersection, dstlist)
        for r in results:
            end.add(asm_instr_dict[r])

        paths = []
        if len(start) != 0 and len(end) != 0:
            for s in list(start):
                for e in list(end):
                    path = self.__find_path(self._gadget_graph, s, e)
                    paths += list(path)

        # Sort by the key of instruction's length
        paths = sorted(paths, key=lambda path: len("; ".join([str(dinstr.asm_instr) \
                        for x in path  for dinstr in x.instrs])))
        if len(paths) > 0:
            return paths
        else:
            return None

    def __find_path(self, graph, start, end, path=[]):
        '''DFS for find a path in gadget graph.
        '''
        path = path + [start]

        if start == end:
            yield path
        if not graph.has_key(start):
            return
        for node in graph[start]:
            if node not in path:
                for new_path in self.__find_path(graph, node, end, path):
                    if new_path:
                        yield new_path



    def __verify_path(self, path, cond=[]):
        '''Verify paths, get the rsp(esp) jump value, and the value on stack.
        '''
        return self.verifier._verify_path(path, cond)

    def __load_x86_gadgets(self):
        """Load all ROP gadgets for the selected ELF files
        New feature: 1. Without ROPgadget
                     2. Extract all gadgets, including ret, jmp, call, syscall, sysenter.
        """

        out = []
        #elf = self.elf
        gadget_RE = [
                        ["\xc3", 1, 1],               # ret
                        #["\xc2[\x00-\xff]{2}", 3, 1],  # ret <imm>
                        #["\xff[\x20\x21\x22\x23\x26\x27]{1}", 2, 1], # jmp  [reg]
                        #["\xff[\xe0\xe1\xe2\xe3\xe4\xe6\xe7]{1}", 2, 1], # jmp  [reg]
                        #["\xff[\x10\x11\x12\x13\x16\x17]{1}", 2, 1], # jmp  [reg]
                        #["\xff[\xd0\xd1\xd2\xd3\xd4\xd6\xd7]{1}", 2, 1],  # call  [reg]
                        #["\xcd\x80", 2, 1], # int 0x80
                        #["\x0f\x34", 2, 1], # sysenter
                        #["\x0f\x05", 2, 1], # syscall
                        ]
        for elf in self.elfs:
            gadgets = []
            for seg in elf.executable_segments:
                gadgets += self.__find_all_gadgets(seg, gadget_RE, elf)
       
            gadgets = self.__passCleanX86(gadgets)
            gadgets = self.__deduplicate(gadgets)

            #build for cache
            data = {}
            for gad in gadgets:
                data[gad["address"]] = gad["bytes"]
            self.__cache_save(elf, data)

            out += gadgets

        return out

    def __load_arm_gadgets(self):

        out = []
        ARM = [
                    ["[\x00-\xff]{1}\x80\xbd\xe8", 4, 4],       # pop {,pc}
                    #["[\x10-\x19\x1e]{1}\xff\x2f\xe1", 4, 4],  # bx   reg
                    #["[\x30-\x39\x3e]{1}\xff\x2f\xe1", 4, 4],  # blx  reg
                    #["\x00-\xff]{3}\xef", 4, 4] # svc
                ]
        ARMThumb = [
                    ["[\x00-\xff]{1}\xbd", 2, 2],                                     # pop {,pc}
                    #["[\x00\x08\x10\x18\x20\x28\x30\x38\x40\x48\x70]{1}\x47", 2, 2], # bx   reg
                    #["[\x80\x88\x90\x98\xa0\xa8\xb0\xb8\xc0\xc8\xf0]{1}\x47", 2, 2], # blx  reg
                    #["\x00-\xff]{1}\xef", 2, 2], # svc
                ]

        gt_together = {
                capstone.CS_MODE_ARM: ARM,
                #capstone.CS_MODE_THUMB: ARMThumb
                }

        for m, gadget_RE in gt_together.items():

            self.mode = m
            for elf in self.elfs:
                gadgets = []
                for seg in elf.executable_segments:
                    gadgets += self.__find_all_gadgets(seg, gadget_RE, elf)

                gadgets = self.__deduplicate(gadgets)

                #build for cache
                data = {}
                for gad in gadgets:
                    data[gad["address"]] = gad["bytes"]
                self.__cache_save(elf, data)

                out += gadgets

        return out

    def __find_all_gadgets(self, section, gadgets, elf):
        '''Find gadgets like ROPgadget do.
        '''
        C_OP = 0
        C_SIZE = 1
        C_ALIGN = 2
        
        allgadgets = []
        cache = self.__cache_load(elf)
        if cache:
            for k, v in cache.items():
                md = capstone.Cs(self.arch, self.mode)
                decodes = md.disasm(v, k)
                ldecodes = list(decodes)
                gadget = ""
                for decode in ldecodes:
                    gadget += (decode.mnemonic + " " + decode.op_str + " ; ").replace("  ", " ")
                if len(gadget) > 0:
                    gadget = gadget[:-3]
                    onegad = {}
                    onegad["address"] = k
                    onegad["gad_instr"] = ldecodes
                    onegad["gadget"] = gadget
                    onegad["bytes"] = v
                    allgadgets += [onegad]
            return allgadgets

        for gad in gadgets:
            allRef = [m.start() for m in re.finditer(gad[C_OP], section.data())]
            for ref in allRef:
                for i in range(self.depth):
                    md = capstone.Cs(self.arch, self.mode)
                    #md.detail = True
                    if elf.elftype == 'DYN':
                        startAddress = elf.address + section.header.p_vaddr + ref - (i*gad[C_ALIGN])
                    else:
                        startAddress = section.header.p_vaddr + ref - (i*gad[C_ALIGN])

                    decodes = md.disasm(section.data()[ref - (i*gad[C_ALIGN]):ref+gad[C_SIZE]], 
                                        startAddress)
                    ldecodes = list(decodes)
                    gadget = ""
                    for decode in ldecodes:
                        gadget += (decode.mnemonic + " " + decode.op_str + " ; ").replace("  ", " ")
                    if len(gadget) > 0:
                        gadget = gadget[:-3]
                        if (startAddress % gad[C_ALIGN]) == 0:
                            onegad = {}
                            onegad["address"] = startAddress
                            onegad["gad_instr"] = ldecodes
                            onegad["gadget"] = gadget
                            onegad["bytes"] = section.data()[ref - (i*gad[C_ALIGN]):ref+gad[C_SIZE]]
                            if self.need_filter:
                                allgadgets += self.__filter_for_big_binary_or_elf32(onegad)
                            else:
                                allgadgets += [onegad]

        return allgadgets

    def __checkInstructionBlackListedX86(self, insts):
        bl = ["db", "int3", "call", "jmp", "nop", "jne", "jg", "jge"]
        for inst in insts:
            for b in bl:
                if inst.split(" ")[0] == b:
                    return True 
        return False

    def __checkMultiBr(self, insts, br):
        count = 0
        for inst in insts:
            if inst.split()[0] in br:
                count += 1
        return count

    def __passCleanX86(self, gadgets, multibr=False):
        new = []
        # Only extract "ret" gadgets now.
        #br = ["ret", "int", "sysenter", "jmp", "call"]
        br = ["ret"]
        for gadget in gadgets:
            insts = gadget["gadget"].split(" ; ")
            if len(insts) == 1 and insts[0].split(" ")[0] not in br:
                continue
            if insts[-1].split(" ")[0] not in br:
                continue
            if self.__checkInstructionBlackListedX86(insts):
                continue
            if not multibr and self.__checkMultiBr(insts, br) > 1:
                continue
            if len([m.start() for m in re.finditer("ret", gadget["gadget"])]) > 1:
                continue
            new += [gadget]
        return new
    
    def __deduplicate(self, gadgets):
        new, insts = [], []
        for gadget in gadgets:
            if gadget["gadget"] in insts:
                continue
            insts.append(gadget["gadget"])
            new += [gadget]
        return new

    def __convert_to_REIL(self, gadgets):
        '''Convert raw gadgets into REIL instructions
        '''

        trans_mode_old = self._ir_trans.translation_mode
        self._ir_trans.translation_mode = LITE_TRANSLATION

        new = []
        for gadget in gadgets:
            one = []

            # for debug
            for gad in gadget["gad_instr"]:
                
                asm_instr = self.__to_translate(gad)

                if not asm_instr:
                    continue

                # For ARM, Do not translate the asm instruction. For kindly reading.
                asm_instr_old = deepcopy(asm_instr)

                self._ir_trans.reset()
                try:
                    ins_ir = self._ir_trans.translate(asm_instr)
                except:
                    continue
                one.append(DualInstruction(asm_instr.address, asm_instr_old, ins_ir))

            new += [RawGadget(one)]

        self._ir_trans.translation_mode = trans_mode_old
        self.candidates = new

    def __to_translate(self, gad):
        address = gad.address
        size = gad.size
        mnemonic = gad.mnemonic.decode('ascii')
        op_str = gad.op_str.decode('ascii')
        
        asm = str(mnemonic + " " + op_str).strip()
        if self.arch == capstone.CS_ARCH_X86:
            if asm in ["repne", "rep", "lock", "data16"]:
                asm, size = "", 0

        instr = self._parser.parse(asm) if asm else None

        if instr:
            instr.address = address
            instr.size = size
            instr.bytes = str(gad.bytes)

        return instr

    def __get_cachefile_name(self, elf):
        basename = os.path.basename(elf.file.name)
        sha256   = hashlib.sha256(elf.get_data()).hexdigest()
        cachedir  = os.path.join(tempfile.gettempdir(), 'binjitsu-rop-cache')

        if not os.path.exists(cachedir):
            os.mkdir(cachedir)

        return os.path.join(cachedir, sha256)

    def __cache_load(self, elf):
        filename = self.__get_cachefile_name(elf)

        if not os.path.exists(filename):
            return None

        log.info_once("Loaded cached gadgets for %r" % elf.file.name)
        gadgets = eval(file(filename).read())

        # Gadgets are saved with their 'original' load addresses.
        gadgets = {k-elf.load_addr+elf.address:v for k,v in gadgets.items()}

        return gadgets

    def __cache_save(self, elf, data):
        # Gadgets need to be saved with their 'original' load addresses.
        data = {k+elf.load_addr-elf.address:v for k,v in data.items()}

        file(self.__get_cachefile_name(elf),'w+').write(repr(data))

    def __getattr__(self, attr):
        """Helper to make finding ROP gadets easier.

        Also provides a shorthand for ``.call()``:
            ``rop.function(args)`` is equivalent to ``rop.call(function, args)``

        >>> elf=ELF(which('bash'))
        >>> rop=ROP([elf])
        >>> rop.rdi     == rop.search(regs=['rdi'], order = 'regs')
        True
        >>> rop.r13_r14_r15_rbp == rop.search(regs=['r13','r14','r15','rbp'], order = 'regs')
        True
        >>> rop.ret_8   == rop.search(move=8)
        True
        >>> rop.ret     != None
        True
        """
        bad_attrs = [
            'trait_names',          # ipython tab-complete
            'download',             # frequent typo
            'upload',               # frequent typo
        ]

        if attr in self.__dict__ \
        or attr in bad_attrs \
        or attr.startswith('_'):
            raise AttributeError('ROP instance has no attribute %r' % attr)


        #
        # Check for a '_'-delimited list of registers
        #
        reg_suffixes = []
        if self.bin.binary.architecture == arch.ARCH_X86:
            reg_suffixes = ['ax', 'bx', 'cx', 'dx', 'bp', 'sp', 'di', 'si',
                            'r8', 'r9', '10', '11', '12', '13', '14', '15']
        elif self.bin.binary.architecture == arch.ARCH_ARM:
            reg_suffixes = ["r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9",
                            "10", "11", "12", "13", "14", "15", "sp", "lr", "pc", "fp"]

        if all(map(lambda x: x[-2:] in reg_suffixes, attr.split('_'))):
            regs = attr.split('_')
            regmaps = self.bin.arch_info.alias_mapper
            gadgets = self.search(regmaps["sp"][0], regs = attr.split('_'))
            if gadgets:
                self.__pretty_print(gadgets)
            return gadgets

        #
        # Otherwise, assume it's a rop.call() shorthand
        #
        def call(*args):
            return self.call(attr,args)
        return call

    def __pretty_print(self, gadgets=[]):

        i = 0
        for gad in gadgets:
            print "[%d]: " % i,
            for g in gad:
                print hex(g.address), "; ".join([str(dinstr.asm_instr) for dinstr in g.instrs])
            i += 1

