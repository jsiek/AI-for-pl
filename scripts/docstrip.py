"""Minimal docstrip (a reimplementation of LaTeX's docstrip, for containers
without TeX).

Usage: python3 docstrip.py SOURCE.dtx OPTION,OPTION,... OUTPUT

Validated byte for byte against docstrip output: acmart.cls v1.60 and
v2.16, sample-acmsmall-conf.tex v2.16 (SystemF/agda/strong-rep-nu/paper/
README.md).  Also: %<<TAG ... %TAG verbatim blocks; runs of empty input
lines count once; trailing spaces are stripped; the docstrip header and
footer are written, with \\endinput appended if missing.

The rules: extract guarded code from a .dtx, as LaTeX's docstrip does.
  %<*expr> ... %</expr>   block, included when expr (and all enclosing blocks) hold
  %<expr>text / %<+expr>text   line included when expr holds
  %<-expr>text            line included when expr does not hold
  %%...                   meta-comment, copied when the enclosing blocks hold
  %...                    comment, dropped
  other lines             code, copied when the enclosing blocks hold
Expressions: names, ! (not), & (and), | and , (or), parentheses."""
import re,sys
def evaluate(expr, opts):
    toks=re.findall(r'[A-Za-z0-9_\-]+|[!&|,()]', expr.replace(' ',''))
    pos=[0]
    def peek(): return toks[pos[0]] if pos[0]<len(toks) else None
    def eat(): t=toks[pos[0]]; pos[0]+=1; return t
    def orx():
        v=andx()
        while peek() in ('|',','): eat(); v=andx() or v
        return v
    def andx():
        v=notx()
        while peek()=='&': eat(); v=notx() and v
        return v
    def notx():
        if peek()=='!': eat(); return not notx()
        if peek()=='(':
            eat(); v=orx(); assert eat()==')'; return v
        return eat() in opts
    v=orx(); assert pos[0]==len(toks), expr; return v
def strip(path, opts):
    out=[]; stack=[]; verb=None; prev_empty=False
    for line in open(path, encoding='utf-8').read().split('\n'):
        line=line.rstrip(' ')
        active=all(v for _,v in stack)
        if verb is not None:                 # inside %<<TAG ... %TAG
            if line=='%'+verb: verb=None
            elif active: out.append(line)
            prev_empty=False; continue
        if line=='':                         # runs of empty input lines count once
            if not prev_empty and active: out.append(line)
            prev_empty=True; continue
        prev_empty=False
        if line.startswith('%<<'):
            verb=line[3:]; continue
        m=re.match(r'^%<([*/+\-]?)([^>]*)>(.*)$', line)
        if m:
            kind,expr,rest=m.groups()
            if kind=='*': stack.append((expr, evaluate(expr,opts)))
            elif kind=='/':
                e,_=stack.pop(); assert e==expr, (e,expr)
            elif kind in ('','+'):
                if active and evaluate(expr,opts): out.append(rest)
            else:
                if active and not evaluate(expr,opts): out.append(rest)
        elif line.startswith('%%'):
            if active: out.append(line)
        elif line.startswith('%'):
            pass
        else:
            if active: out.append(line)
    assert not stack, stack
    while out and out[-1]=='': out.pop()
    return out
HEADER='''%%
%% This is file `{dst}',
%% generated with the docstrip utility.
%%
%% The original source files were:
%%
%% {src}  (with options: `{opts}')
%% 
%% IMPORTANT NOTICE:
%% 
%% For the copyright see the source file.
%% 
%% Any modified versions of this file must be renamed
%% with new filenames distinct from {dst}.
%% 
%% For distribution of the original source see the terms
%% for copying and modification in the file {src}.
%% 
%% This generated file may be distributed as long as the
%% original source files, as listed above, are part of the
%% same distribution. (The sources need not necessarily be
%% in the same archive or directory.)'''
if __name__=='__main__':
    import os
    src,optstr,dst=sys.argv[1],sys.argv[2],sys.argv[3]
    name=os.path.basename(dst); srcname=os.path.basename(src)
    body=strip(src,set(optstr.split(',')))
    if not body or body[-1]!='\\endinput': body.append('\\endinput')
    text=HEADER.format(dst=name,src=srcname,opts=optstr)+'\n'+'\n'.join(body)+'\n%%\n%% End of file `'+name+"'.\n"
    open(dst,'w',encoding='utf-8').write(text)
