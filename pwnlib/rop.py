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

from .elf     import ELF
from .util    import packing
from .log     import getLogger

from operator import itemgetter

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

    def __init__(self, code_analyzer, architecture_info):
        self.STACK_MAX_LEN = 1024
        super(VerifyROP, self).__init__(code_analyzer, architecture_info)

    #first resolvable, second the path to resolve
    def _verify_path(self, paths, cond=[]):

        result = []
        for path in paths:
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
            if self._arch_info.architecture_mode == arch.ARCH_X86_MODE_64:
                sat, rsp, stack_result = self._satisfy_x64(cond)
            elif self._arch_info.architecture_mode == arch.ARCH_X86_MODE_32:
                sat, rsp, stack_result = self._satisfy_x86(cond)

            if sat:
                result.append((path, rsp, stack_result))

        return result

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
        if flag:
            rbp_pre = self.analyzer.get_register_expr("rbp", mode="pre")
            self.analyzer.set_precondition(rbp_pre == 0xdeadbeef)
            rbp_con = self.analyzer.get_memory_expr(rbp_pre, 8)
            self.analyzer.set_precondition(rbp_con == 0xbeef0000)

            rbp_post = self.analyzer.get_register_expr("rbp", mode="post")
            self.analyzer.set_postcondition(rbp_post == 0xdeadbeef)

        rsp_pre = self.analyzer.get_register_expr("rsp", mode="pre")
        rsp_post = self.analyzer.get_register_expr("rsp", mode="post")
        self.analyzer.set_precondition(rsp_pre == 0)

        stack = []
        for i in xrange(self.STACK_MAX_LEN):
            stack.append(self.analyzer.get_memory_expr(rsp_pre + i*8, 8))


        stack_result = []
        if self.analyzer.check() == 'sat':
            for i in xrange(len(stack)):
                t = self.analyzer.get_expr_value(stack[i])
                if t != 0:
                    stack_result.append((i, t))

            rsp_val = self.analyzer.get_expr_value(rsp_post)

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
        if flag:
            rbp_pre = self.analyzer.get_register_expr("ebp", mode="pre")
            self.analyzer.set_precondition(ebp_pre == 0xdeadbeef)
            ebp_con = self.analyzer.get_memory_expr(ebp_pre, 4)
            self.analyzer.set_precondition(ebp_con == 0xbeef0000)

            ebp_post = self.analyzer.get_register_expr("ebp", mode="post")
            self.analyzer.set_postcondition(ebp_post == 0xdeadbeef)

        esp_pre = self.analyzer.get_register_expr("esp", mode="pre")
        esp_post = self.analyzer.get_register_expr("esp", mode="post")
        self.analyzer.set_precondition(esp_pre == 0)

        stack = []
        for i in xrange(self.STACK_MAX_LEN):
            stack.append(self.analyzer.get_memory_expr(esp_pre + i*4, 4))

        stack_result = []
        if self.analyzer.check() == "sat":
            for i in xrange(len(stack)):
                t = self.analyzer.get_expr_value(stack[i])
                if t != 0:
                    stack_result.append((i, t))

            esp_val = self.analyzer.get_expr_value(esp_post)

            return (True, esp_val, stack_result)
        else:
            return (False, 0, [])

class ROP():

    def __init__(self, filename, byte_depth=20, instrs_depth=7):
        self.bin = BARF(filename)

        self.elf = ELF(filename)
        self.depth = 10
        self._ir_trans = self.bin.ir_translator
        self._parser = self.bin.disassembler._parser
        self.verifier = VerifyROP(self.bin.code_analyzer, self.bin.arch_info)

        #find gadgets.
        self.candidates = None

        self.need_filter = False
        if len(self.elf.file.read()) >= MAX_SIZE*1000:
            self.need_filter = True

        if self.bin.binary.architecture == arch.ARCH_X86:
            self.arch = capstone.CS_ARCH_X86
            if self.bin.binary.architecture_mode == arch.ARCH_X86_MODE_64:
                self.mode = capstone.CS_MODE_64
            elif self.bin.binary.architecture_mode == arch.ARCH_X86_MODE_32:
                self.need_filter = True
                self.mode = capstone.CS_MODE_32
            gadgets = self._load_x86_gadgets()
            self.__convert_to_REIL(gadgets)
        elif self.bin.binary.architecture == arch.ARCH_ARM:
            self.arch = capstone.CS_ARCH_ARM
            pass
        
        # Using BARF to find gadgets, but it's too slow for large binary.
        #self.candidates = self.bin.gadget_finder.find(self.bin.binary.ea_start, 
                                                    #self.bin.binary.ea_end,
                                                    #byte_depth=byte_depth,
                                                    #instrs_depth=instrs_depth)
        ###filter duplicate gadgets
        #self.candidates = self.filter_duplicates()

        #classified the gadgets
        self.classified = self.do_classify()

        #verify the gadgets
        self.verified = self.do_verify()

        self._chain = []
        self._gadget_graph = {}
        self._build_graph()

    def __filter_for_big_binary_or_elf32(self, gadgets):
        '''Filter gadgets for big binary.
        '''
        new = []
        pop   = re.compile(r'^pop (.{3})')
        add   = re.compile(r'^add .sp, (\S+)$')
        ret   = re.compile(r'^ret$')
        leave = re.compile(r'^leave$')

        valid = lambda insn: any(map(lambda pattern: pattern.match(insn), [pop,add,ret,leave]))

        insns = [g.strip() for g in gadgets["gadget"].split(";")]
        if all(map(valid, insns)):
            new.append(gadgets)

        return new

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
    
    def _find_suitable_gg(self, gg, arglen):
        '''Find gadgets, which esp jump just >= argument_length*4 + 4(ret) 
        '''
        for g, jump, _ in gg:
            if jump >= arglen*4 + 4:
                return (True, g, jump)

        print "Cannot find out suitable gadget."
        return (False, 0, 0)

    def build(self):
        '''Automatic build rop chain for binary.
        '''
        result = ""
        if self.bin.binary.architecture == arch.ARCH_X86:
            if self.bin.binary.architecture_mode == arch.ARCH_X86_MODE_32:
                result = self.__build_x86()
            elif self.bin.binary.architecture_mode == arch.ARCH_X86_MODE_64:
                result = self.__build_x64()
        else:
            raise NotImplementedError(self.__class__.__name__ + '.do_something')

        return result

    def __build_x86(self):
        '''Build rop chain for elf x86.
        '''
        padding = ""

        gg = self._verify_path(self._find_x86_paths())
        gg = sorted(gg, key=itemgetter(1))

        for index, (addr, arguments)  in enumerate(self._chain):
            padding += struct.pack("<I", addr)
            if not isinstance(arguments, tuple):
                arguments = (arguments,)
            arglen = len(arguments)
            
            r, g, jump = self._find_suitable_gg(gg, arglen)
            if r:
                compensation = jump - arglen - 4
                padding += struct.pack("<I", g[0].address)

                # for debug
                print hex(g[0].address), \
                        "jump: ", jump,\
                        "; ".join([str(dinstr.asm_instr) for dinstr in g[0].instrs])

                for i in xrange(jump/4 - 1):
                    if i < arglen:
                        if isinstance(arguments[i], int):
                            padding += struct.pack("<i", arguments[i])
                        elif isinstance(arguments[i], str):
                            padding += arguments[i]
                    else:
                        padding += "A"*(compensation)

        return padding

    def __build_x64(self):
        '''Build rop chain for elf x86.
        '''
        padding = ""

        # The number of Arguments more than 6 ! Are you crazy?
        # For GCC now, TODO: windows & mach
        regs = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]

        for index, (addr, arguments) in enumerate(self._chain):
            if not isinstance(arguments, tuple):
                arguments = (arguments,)
            arglen = len(arguments)
            for i in range(arglen):
                gadget = self.search("rsp", [regs[i]])[0]
                if not gadget:
                    print "gadget to reg %s not found!" % regs[i]
                    sys.exit(0)

                # for debug
                print hex(gadget[0].address), \
                        "; ".join([str(dinstr.asm_instr) for x in gadget for dinstr in x.instrs])

                result = self._verify_path([gadget], cond=[(regs[i], arguments[i])])
                # TODO: how about arrangement gadgets number > 2
                result = result[0]
                path, rsp, stack_result = result
                padding += struct.pack("<Q", path[0].address)
                
                temp_padding = ""
                for i in range(rsp-8):
                    temp_padding += "A"

                for pos, value in stack_result:
                    pos = pos * 8
                    temp_padding = temp_padding[:pos] + struct.pack("<Q", value) + temp_padding[pos + 8:]

                padding += temp_padding

            ret_address = struct.pack("<Q", addr)
            padding += ret_address

        return padding

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

    def _build_graph(self):
        '''Build gadgets graph, gadget as vertex, reg as edge.
        '''
        for instr in self.verified:

            dst = []
            regmaps = self.bin.arch_info.alias_mapper
            op_size = self.bin.arch_info.operand_size
            for s in instr.destination:
                if s.size != op_size:
                    dst.append(regmaps[str(s)][0])
                else:
                    dst.append(str(s))
            for instr_b in self.verified:
                if instr == instr_b:
                    break
                
                src = []
                for s in instr_b.sources:
                    if isinstance(s, ReilRegisterOperand):
                        if s.size != op_size:
                            src.append(regmaps[str(s)][0])
                        else:
                            src.append(str(s))
                instr_xor = list(set(dst) & set(src))
                if len(instr_xor) != 0:
                    try:
                        self._gadget_graph[instr].add(instr_b)
                    except KeyError:
                        self._gadget_graph[instr] = set()

    def __find_x86_paths(self):
        '''Search paths for ELF32, now only support single instruction arrangement.
        TODO: two more gadgets arrangement support.
        '''
        return [ [instr] for instr in self.verified]


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
        for instr in self.verified:
            instr_dsts = [str(s) for s in instr.destination]
            if (set(instr_dsts) & set(regs)) == set(regs):
                end.add(instr)

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

    def _verify_path(self, paths, cond=[]):
        '''Verify paths, get the rsp(esp) jump value, and the value on stack.
        '''
        return self.verifier._verify_path(paths, cond)

    def _load_x86_gadgets(self):
        """Load all ROP gadgets for the selected ELF files
        New feature: 1. Without ROPgadget
                     2. Extract all gadgets, including ret, jmp, call, syscall, sysenter.
        """
        #self._parser = X86Parser(architecture_mode=self.bin.binary.architecture_mode)


        gadgets = []
        elf = self.elf
        ROPgadget = [
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
        for seg in elf.executable_segments:
            gadgets += self._find_all_gadgets(seg, ROPgadget)
       
        gadgets = self.__passCleanX86(gadgets)
        gadgets = self.__deduplicate(gadgets)

        #build for cache
        data = {}
        for gad in gadgets:
            data[gad["address"]] = gad["bytes"]
        self.__cache_save(self.elf, data)

        return gadgets

    def _find_all_gadgets(self, section, gadgets):
        '''Find gadgets like ROPgadget do.
        '''
        C_OP = 0
        C_SIZE = 1
        C_ALIGN = 2
        
        allgadgets = []
        cache = self.__cache_load(self.elf)
        if cache:
            for k, v in cache.items():
                md = capstone.Cs(self.arch, self.mode)
                md.detail = True
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
                    md.detail = True
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

                self._ir_trans.reset()
                try:
                    ins_ir = self._ir_trans.translate(asm_instr)
                except:
                    continue
                one.append(DualInstruction(asm_instr.address, asm_instr, ins_ir))

            new += [RawGadget(one)]

        self._ir_trans.translation_mode = trans_mode_old
        self.candidates = new

    def __to_translate(self, gad):
        address = gad.address
        size = gad.size
        mnemonic = gad.mnemonic.decode('ascii')
        op_str = gad.op_str.decode('ascii')

        asm = str(mnemonic + " " + op_str).strip()
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
        # Check for 'ret' or 'ret_X'
        #
        if attr.startswith('ret'):
            count = 4
            if '_' in attr:
                count = int(attr.split('_')[1])

            return self.search(move=count)

        #
        # Check for a '_'-delimited list of registers
        #
        x86_suffixes = ['ax', 'bx', 'cx', 'dx', 'bp', 'sp', 'di', 'si',
                        'r8', 'r9', '10', '11', '12', '13', '14', '15']
        if all(map(lambda x: x[-2:] in x86_suffixes, attr.split('_'))):
            gadgets = self.search("rsp", regs = attr.split('_'))
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

if __name__ == "__main__":
    ctime = time.time()

    #rop = ROP("libc.so.6")
    debug_64 = False
    
    if debug_64:
        rop = ROP("../start/pizza")
        rop.for_debug_d()

        # 64bit testing.
        gadget = rop.search("rsp", ["rdi"])[0]
        print "; ".join([str(dinstr.asm_instr) for x in gadget for dinstr in x.instrs])

        rop.call(0xdeadbeef, (0x7fff87654321))
        rop.call(0xffffffff44444444, (0x111, 0x222))
        result = rop.build()
        print result
        print result.encode("hex")
    else:
        # 32bit testing
        rop = ROP("../start/pwn200")
        rop.for_debug_d()
        rop.call(0xdeadbeef, (1,2,3))
        rop.call(0xaaaabbbb, (5555, -2))
        rop.call(0xddddcccc, (0x7fffffff))
        result = rop.build()
        print result
        print result.encode('hex')

    ctime = time.time() - ctime

    print "Total time: ", ctime

