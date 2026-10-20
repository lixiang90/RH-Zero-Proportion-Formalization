"""Windows loader-only debugger protocol. Prepared, never executed in preparation.

Create only this helper's new trusted child; stop at the automatic initial
breakpoint, collect mapped DLL paths, terminate it before DLL init/application
entry, and observe the owned process handle exit. No attach to existing PIDs.
Microsoft initial-breakpoint contract is linked in README.
"""
import ctypes as C
from ctypes import wintypes as W
from pathlib import Path
import subprocess
import time

PTR=C.c_void_p
SIZE=C.c_size_t
class STARTUP(C.Structure):
    _fields_=[('cb',W.DWORD),('reserved',W.LPWSTR),('desktop',W.LPWSTR),('title',W.LPWSTR),
        ('x',W.DWORD),('y',W.DWORD),('xs',W.DWORD),('ys',W.DWORD),('xc',W.DWORD),('yc',W.DWORD),
        ('fill',W.DWORD),('flags',W.DWORD),('show',W.WORD),('reserved2size',W.WORD),
        ('reserved2',PTR),('stdin',W.HANDLE),('stdout',W.HANDLE),('stderr',W.HANDLE)]
class PROCESS(C.Structure):
    _fields_=[('process',W.HANDLE),('thread',W.HANDLE),('pid',W.DWORD),('tid',W.DWORD)]
class EX_RECORD(C.Structure):
    _fields_=[('code',W.DWORD),('flags',W.DWORD),('record',PTR),('address',PTR),
              ('number',W.DWORD),('parameters',SIZE*15)]
class EX_INFO(C.Structure):
    _fields_=[('record',EX_RECORD),('first',W.DWORD)]
class CREATE_INFO(C.Structure):
    _fields_=[('file',W.HANDLE),('process',W.HANDLE),('thread',W.HANDLE),('base',PTR),
        ('debug_offset',W.DWORD),('debug_size',W.DWORD),('tls',PTR),('start',PTR),
        ('image_name',PTR),('unicode',W.WORD)]
class LOAD_INFO(C.Structure):
    _fields_=[('file',W.HANDLE),('base',PTR),('debug_offset',W.DWORD),('debug_size',W.DWORD),
              ('image_name',PTR),('unicode',W.WORD)]
class DATA(C.Union):
    _fields_=[('exception',EX_INFO),('create',CREATE_INFO),('load',LOAD_INFO),('exit_code',W.DWORD),('raw',C.c_byte*160)]
class EVENT(C.Structure):
    _fields_=[('code',W.DWORD),('pid',W.DWORD),('tid',W.DWORD),('data',DATA)]


def probe(executable,env,cwd,timeout=30):
    k=C.WinDLL('kernel32',use_last_error=True)
    k.CreateProcessW.argtypes=[W.LPCWSTR,W.LPWSTR,PTR,PTR,W.BOOL,W.DWORD,PTR,W.LPCWSTR,C.POINTER(STARTUP),C.POINTER(PROCESS)]
    k.CreateProcessW.restype=W.BOOL
    k.WaitForDebugEvent.argtypes=[C.POINTER(EVENT),W.DWORD];k.WaitForDebugEvent.restype=W.BOOL
    k.ContinueDebugEvent.argtypes=[W.DWORD,W.DWORD,W.DWORD];k.ContinueDebugEvent.restype=W.BOOL
    k.TerminateProcess.argtypes=[W.HANDLE,W.UINT];k.TerminateProcess.restype=W.BOOL
    k.CloseHandle.argtypes=[W.HANDLE];k.CloseHandle.restype=W.BOOL
    k.WaitForSingleObject.argtypes=[W.HANDLE,W.DWORD];k.WaitForSingleObject.restype=W.DWORD
    k.GetExitCodeProcess.argtypes=[W.HANDLE,C.POINTER(W.DWORD)];k.GetExitCodeProcess.restype=W.BOOL
    k.GetFinalPathNameByHandleW.argtypes=[W.HANDLE,W.LPWSTR,W.DWORD,W.DWORD]
    k.GetFinalPathNameByHandleW.restype=W.DWORD
    k.K32EnumProcessModulesEx.argtypes=[W.HANDLE,C.POINTER(PTR),W.DWORD,C.POINTER(W.DWORD),W.DWORD]
    k.K32EnumProcessModulesEx.restype=W.BOOL
    k.K32GetModuleFileNameExW.argtypes=[W.HANDLE,PTR,W.LPWSTR,W.DWORD]
    k.K32GetModuleFileNameExW.restype=W.DWORD
    start=STARTUP();start.cb=C.sizeof(start);process=PROCESS()
    line=C.create_unicode_buffer(subprocess.list2cmdline([str(executable)]))
    block=C.create_unicode_buffer('\0'.join(key+'='+value for key,value in sorted(env.items(),key=lambda r:r[0].casefold()))+'\0\0')
    if not k.CreateProcessW(str(executable),line,None,None,False,0x2|0x400|0x200,
                           block,str(cwd),C.byref(start),C.byref(process)):
        raise C.WinError(C.get_last_error())
    deadline=time.monotonic()+timeout;initial=False;exited=False;paths=[];events=[]
    try:
        while time.monotonic()<deadline:
            event=EVENT()
            if not k.WaitForDebugEvent(C.byref(event),max(1,int((deadline-time.monotonic())*1000))):
                raise C.WinError(C.get_last_error())
            if event.pid!=process.pid:raise RuntimeError('Unexpected child PID in own debug session')
            events.append({'code':event.code,'pid':event.pid,'tid':event.tid})
            handle=event.data.create.file if event.code==3 else event.data.load.file if event.code==6 else None
            if handle:
                try:
                    buffer=C.create_unicode_buffer(32768)
                    if not k.GetFinalPathNameByHandleW(handle,buffer,len(buffer),0):raise C.WinError(C.get_last_error())
                    name=buffer.value
                    if name.startswith('\\\\?\\'):name=name[4:]
                    paths.append(str(Path(name).absolute()))
                finally:k.CloseHandle(handle)
            if event.code==1:
                if event.data.exception.record.code!=0x80000003 or initial:
                    raise RuntimeError('Unexpected exception before controlled initial breakpoint')
                initial=True
                modules=(PTR*4096)();needed=W.DWORD()
                if not k.K32EnumProcessModulesEx(process.process,modules,C.sizeof(modules),C.byref(needed),3):
                    raise C.WinError(C.get_last_error())
                if needed.value>C.sizeof(modules):raise RuntimeError('Module buffer too small')
                for module in modules[:needed.value//C.sizeof(PTR)]:
                    name=C.create_unicode_buffer(32768)
                    if not k.K32GetModuleFileNameExW(process.process,module,name,len(name)):
                        raise C.WinError(C.get_last_error())
                    paths.append(str(Path(name.value).absolute()))
                if not k.TerminateProcess(process.process,222):raise C.WinError(C.get_last_error())
            if not k.ContinueDebugEvent(event.pid,event.tid,0x00010002):raise C.WinError(C.get_last_error())
            if event.code==5:
                exited=True;break
        if not initial or not exited:raise RuntimeError('No complete loader-breakpoint/owned-exit protocol')
        if k.WaitForSingleObject(process.process,5000)!=0:raise RuntimeError('Owned process not signaled terminal')
        code=W.DWORD()
        if not k.GetExitCodeProcess(process.process,C.byref(code)) or code.value!=222:
            raise RuntimeError('Unexpected owned loader-probe termination status')
        return {'executable':str(executable),'owned_pid':process.pid,'initial_breakpoint_observed':True,
            'target_main_or_DLL_initialization_executed':False,'owned_terminal_exit_code':code.value,
            'loaded_PE_paths':sorted(set(paths),key=str.casefold),'debug_events':events}
    finally:
        if not exited:
            k.TerminateProcess(process.process,223)
            k.WaitForSingleObject(process.process,5000)
        k.CloseHandle(process.thread);k.CloseHandle(process.process)
