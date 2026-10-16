"""Measure the current complete-source encoding without publishing an upload.

Passing the finite input binding is not a Lean proof. This script records
exact assembled bytes and whether they fit the website's source boundary.
"""
from pathlib import Path
import hashlib,json
import bundle
from final_artifact_gate import finite_binding

HERE=Path(__file__).resolve().parent

def main():
    if not __debug__:raise RuntimeError('Size assessment assertions must remain enabled')
    binding=finite_binding()
    source,hashes,imports,readable,meta=bundle.compressed_bundle(True,True,True,32768)
    raw=source.encode('utf8')
    result={'scope':__doc__,'finite_certificate_binding':binding,
        'source_modules_sha256':hashes,'imports':imports,
        'assembled_source_bytes':len(raw),'assembled_source_sha256':hashlib.sha256(raw).hexdigest(),
        'website_max_source_bytes':2000000,'website_source_size_passed':len(raw)<=2000000,
        'excess_source_bytes':max(0,len(raw)-2000000),
        'source_file_published':False,'complete_tree_lean_checked':False,
        'upload_ready':False,'higher_kappa_proven':False,
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),**meta}
    (HERE/'submission-size-assessment.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['assembled_source_bytes','website_source_size_passed','excess_source_bytes','upload_ready']}))

if __name__=='__main__':main()
