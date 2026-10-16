"""Deterministically bundle W10, retaining the generic inherited proof and tables.

This does not modify the frozen Core.  Every retained slice is verbatim; only
the unused old nine-point instance, data and W9 bridge are omitted.
The resulting single file requires a fresh isolated compilation and replay.
"""
from pathlib import Path
import argparse,hashlib,json,re,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from bundle_gram_defect_solution import strip_imports,remaining_sections,code_mask

def trimmed_core(prune=False,encoded=False):
    p=ROOT/'GramDefect20261015/Core.lean'; raw=p.read_bytes();s=raw.decode('utf8')
    assert hashlib.sha256(raw).hexdigest()=='2062b1f9540e1ea7b78d382f46a234780dcda03f4e3a6c21467c84b611505ff5'
    a=s.index('-- SWAP BEGIN certificate');z=s.index('-- SWAP END certificate')
    ha=s.index('noncomputable section\nnamespace AMW.Cert.PCell\nopen AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD\ndef pwD ',a)
    hz=s.index('end AMW.Cert.PCell\nend\n',ha)+len('end AMW.Cert.PCell\nend\n')
    da=s.index('set_option Elab.async false\nnoncomputable section\nnamespace AMW.Cert.PC9QB6MData',hz)
    dz=s.index('def COV :',da)
    if prune:
        from prune_core import unused_ranges,prune_slice,report
        ranges=unused_ranges(s);report(s,ranges)
        piece=lambda start,end:prune_slice(s,start,end,ranges)
    else:piece=lambda start,end:s[start:end]
    table=piece(da,dz).replace(' AMW.Cert.PC9QB6M\n','\n')
    replacement=('''/- W10 bundle: the unused old W9 instance and its coverage tree
are omitted.  Used generic PCell helpers, analytic minorant tables and
counting proofs are retained. Unused declarations may also be pruned. -/\n'''+piece(ha,hz)+table+
      'end AMW.Cert.PC9QB6MData\nend\n'+
      'namespace RiemannFail\nopen Zeta23Ext.Bridge\n'+
      'theorem cert_wfun_eq (x : ℝ) : AMW.Cert.wfun x = wfun x := rfl\n'+
      'end RiemannFail\n')
    result=piece(0,a)+replacement+piece(z,len(s))
    assert result[result.index('/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS'):]==s[s.index('/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS'):]
    assert 'PC9QB6M.' not in code_mask(result)
    assert remaining_sections(result)==remaining_sections(s)
    if encoded:
        from emit_tree import encode
        mask=code_mask(result)
        hits=list(re.finditer(r'\b0x[0-9a-fA-F]{24,}\b',mask))
        for hit in reversed(hits):
            result=result[:hit.start()]+'(~"'+encode(int(hit.group(),16))+'")'+result[hit.end():]
    return result

BASE_MODULES=['GramDefect20261015.Core','GramDefect20261015.SharpWindow',
 'GramDefect20261015.RefinedCounting','StructuralResearch20261016.Coboundary',
 'StructuralResearch20261016.CoboundaryCounting','StructuralResearch20261016.W10RefinedCandidate',
 'StructuralW10Cert20261016.LocalChecker','StructuralW10Cert20261016.TreeCoverage',
 'StructuralW10Cert20261016.RootBounds','StructuralW10Cert20261016.Reflection',
 'StructuralW10Cert20261016.FinalConditional','StructuralW10Cert20261016.FloorTransfer']

COMPLETE_MODULES=['StructuralW10Cert20261016.NumeralCodec',*BASE_MODULES,
 'StructuralW10Cert20261016.CompactLeaf','StructuralW10Cert20261016.RelCompactLeaf',
 'StructuralW10Cert20261016.EncodedLiteral','StructuralW10Cert20261016.OrderCoverage',
 'StructuralW10Cert20261016.LeafDispatch','StructuralW10Cert20261016.FastPruefer',
 'StructuralW10Cert20261016.ForcedCoverage','StructuralW10Cert20261016.AdaptiveCoverage',
 'StructuralW10Cert20261016.Certificate','StructuralW10Cert20261016.Final']

def wrapper():
    return '''
noncomputable section
namespace W10SubmissionCounts
theorem count_eq (a b : ℝ) : _root_.Ncount a b = Zeta23.Ncount a b := by rfl
theorem distinct_eq (a b : ℝ) : _root_.N0star a b = Zeta23.N0star a b := by rfl
end W10SubmissionCounts
theorem candidate_strict_improvement : currentRecordKappa < candidateKappa := by
  norm_num [currentRecordKappa, candidateKappa]
theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2*T) : ℝ) ≤ N0star T (2*T) := by
  simpa only [candidateKappa, StructuralW10Cert20261016.Final.ratio,
    StructuralW10Cert20261016.FinalConditional.candidateRatio,
    W10SubmissionCounts.count_eq, W10SubmissionCounts.distinct_eq]
    using StructuralW10Cert20261016.Final.distinct_dyadic
theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  simpa only [candidateKappa, StructuralW10Cert20261016.Final.ratio,
    StructuralW10Cert20261016.FinalConditional.candidateRatio,
    W10SubmissionCounts.count_eq, W10SubmissionCounts.distinct_eq]
    using StructuralW10Cert20261016.Final.distinct_cumulative
end
'''

def bundle(modules=BASE_MODULES,wrapper='',prune=False,encoded=False):
    imports={'ChallengeDeps','ChallengeDeps.CandidateSpec'} if wrapper else set();blocks=[];hashes={}
    for k,m in enumerate(modules):
        p=ROOT/Path(*m.split('.')).with_suffix('.lean');raw=p.read_bytes()
        hashes[str(p.relative_to(ROOT)).replace('\\','/')]=hashlib.sha256(raw).hexdigest()
        s=trimmed_core(prune,encoded) if m=='GramDefect20261015.Core' else raw.decode('utf8')
        body,im=strip_imports(s);imports.update(im)
        blocks.append(f'/- Source: {m} -/\nsection W10Bundle{k}\n'+body+
          '\n'+'end\n'*remaining_sections(body)+f'end W10Bundle{k}\n')
    imports={i for i in imports if not i.startswith(('GramDefect20261015.','StructuralResearch20261016.','StructuralW10Cert20261016.'))}
    source=('''/- Copyright (c) 2026 Li Xiang (lixiang90), modifications. Apache-2.0.
Ten-point window certificate with exact integer finite coverage.
Generated by research-20261016-w10-cert/bundle.py. Inherited attribution
and license notices are retained. The obsolete W9 instance is omitted.
The website supplies candidateKappa and currentRecordKappa. -/\n'''+
      '\n'.join('import '+i for i in sorted(imports))+'\n'+
      'set_option Elab.async false\nset_option linter.all false\n'+ '\n'.join(blocks)+wrapper)
    assert remaining_sections(source)==0
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',code_mask(source))
    return source,hashes,sorted(imports)

def compressed_bundle(complete,prune,encoded,source_block_bytes=32768):
    """Expand the proof base through a pure source macro; retain data as Nat literals.

    The expanded source is saved alongside the upload and is the readable
    review/reproduction artifact.  The exact uploaded bytes require their own
    compilation, Comparator and independent kernel replay.
    """
    from lzss_source import command
    from source_blocks import scope_blocks
    base_modules=[m for m in COMPLETE_MODULES if m not in [
        'StructuralW10Cert20261016.NumeralCodec','StructuralW10Cert20261016.Certificate',
        'StructuralW10Cert20261016.Final']]
    if not complete:base_modules=BASE_MODULES
    math,hashes,imports=bundle(base_modules,'',prune,encoded)
    body,_=strip_imports(math)
    codec_modules=['StructuralW10Cert20261016.NumeralCodec','StructuralW10Cert20261016.CompressedCommands']
    codecs,ch,ci=bundle(codec_modules)
    codec_body,_=strip_imports(codecs);hashes.update(ch);imports=sorted(set(imports)|set(ci))
    suffix=''
    if complete:
        suffix,sh,si=bundle(['StructuralW10Cert20261016.Certificate','StructuralW10Cert20261016.Final'],wrapper())
        suffix,_=strip_imports(suffix);hashes.update(sh);imports=sorted(set(imports)|set(si))
    header='''/- Copyright (c) 2026 Li Xiang (lixiang90), modifications. Apache-2.0.
The base proof is losslessly encoded below and expanded as ordinary Lean
commands by a pure decoder. No external program, computed proof assumption,
or custom axiom is used. The readable expanded source and all original proof
modules accompany this file in the repository. Full kernel replay is required.
-/\n'''
    raw=body.encode('utf8');raw_blocks=scope_blocks(raw,source_block_bytes)
    commands=[];block_metadata=[]
    for block in raw_blocks:
        encoded_command,data=command(block);commands.append(encoded_command)
        block_metadata.append({'decoded_bytes':len(block),'decoded_sha256':hashlib.sha256(block).hexdigest(),
          'compressed_bytes':len(data),'command_sha256':hashlib.sha256(encoded_command.encode('utf8')).hexdigest()})
    assert b''.join(raw_blocks)==raw
    compressed=''.join(commands)
    # Retain the complete inherited licence trailer in readable form as well.
    core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf8')
    notice=core[core.index('/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS'):]
    attribution=core[:core.index('import ')]
    global_options='set_option Elab.async false\nset_option linter.all false\n'
    source=header+attribution+'\n'.join('import '+i for i in imports)+'\n'+global_options+codec_body+'\n'+compressed+'\n'+suffix+'\n'+notice
    assert remaining_sections(source)==0
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',code_mask(source))
    readable=header+'\n'.join('import '+i for i in imports)+'\n'+global_options+codec_body+'\n'+body+'\n'+suffix
    meta={'expanded_base_bytes':len(raw),'expanded_base_sha256':hashlib.sha256(raw).hexdigest(),
        'compressed_base_bytes':sum(b['compressed_bytes'] for b in block_metadata),
        'encoded_base_source_bytes':len(compressed.encode('utf8')),
        'source_block_target_bytes':source_block_bytes,'source_block_count':len(block_metadata),
        'source_blocks':block_metadata,
        'expanded_source_sha256':hashlib.sha256(readable.encode('utf8')).hexdigest()}
    return source,hashes,imports,readable,meta

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Bundle assertions must remain enabled')
    ap=argparse.ArgumentParser();ap.add_argument('--complete',action='store_true');ap.add_argument('--prune',action='store_true')
    ap.add_argument('--encoded-core',action='store_true');ap.add_argument('--compressed-base',action='store_true')
    ap.add_argument('--source-block-bytes',type=int,default=32768);args=ap.parse_args()
    if args.source_block_bytes<1:ap.error('--source-block-bytes must be positive')
    modules=COMPLETE_MODULES if args.complete else (['StructuralW10Cert20261016.NumeralCodec'] if args.encoded_core else [])+BASE_MODULES
    extra={};readable=None
    if args.compressed_base:
        source,hashes,imports,readable,extra=compressed_bundle(args.complete,args.prune,args.encoded_core,args.source_block_bytes)
    else:source,hashes,imports=bundle(modules,wrapper() if args.complete else '',args.prune,args.encoded_core)
    if args.complete:
        from final_artifact_gate import finite_binding
        extra['finite_certificate_binding']=finite_binding()
        assert hashes['StructuralW10Cert20261016/Certificate.lean']==extra['finite_certificate_binding']['certificate_source_sha256']
        for name,expected in hashes.items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==expected, ('A bundled module changed during assembly',name)
        # This marks assembly only. upload_ready is set by the later verification
        # material generator after all independent checks have passed.
        assert len(source.encode('utf8'))<=2_000_000, 'Source too large: '+str(len(source.encode('utf8')))
        dest=ROOT/'submission/w10-20261016';target=dest/'proof/Solution.lean';target.parent.mkdir(parents=True,exist_ok=True)
    else:target=Path(__file__).with_name('BundlePreflight.lean')
    target.write_bytes(source.encode('utf8'))
    if readable is not None:
        expanded=(dest/'uncompressed/ExpandedSolution.lean') if args.complete else Path(__file__).with_name('ExpandedPreflight.lean')
        expanded.parent.mkdir(parents=True,exist_ok=True);expanded.write_bytes(readable.encode('utf8'))
    result={'source_bytes':len(source.encode('utf8')),'trimmed_core_bytes':len(trimmed_core(args.prune,args.encoded_core).encode('utf8')),
      'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'source_modules_sha256':hashes,
      'assembly_complete':args.complete,'upload_ready':False,'imports':imports,
      'bundle_generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'numerator':'3338842690820594373879991756052499665323','denominator':'4956700000000000000000000000000000000000',**extra}
    if args.complete:(dest/'manifest.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in result.items() if k!='source_modules_sha256'}))
