"""
Network Reachability Analyzer

Build network topologies with a GUI and run DFS-based
bidirectional reachability analysis.
Generates C code, compiles, executes, and displays results.
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog, scrolledtext
import subprocess, os, sys, tempfile, threading, json, math, shutil, signal

NODE_R = 20
COLORS = {
    'source_a':     '#3B82F6',
    'source_b':     '#EF4444',
    'intermediate': '#6B7280',
    'edge_atob':    '#3B82F6',
    'edge_btoa':    '#EF4444',
    'edge_both':    '#8B5CF6',
    'select':       '#F59E0B',
    'mandatory':    '#F59E0B',
    'canvas_bg':    '#F8FAFC',
    'grid':         '#E2E8F0',
}

class Node:
    def __init__(self, name, x, y, role='intermediate',
                 failure_target=True, mandatory=False):
        self.name = name; self.x = x; self.y = y; self.role = role
        self.failure_target = failure_target
        self.mandatory = mandatory

class Edge:
    _counter = 0
    def __init__(self, src, dst, direction='atob',
                 failure_target=True, mandatory=False):
        Edge._counter += 1
        self.eid = Edge._counter; self.src = src; self.dst = dst
        self.direction = direction
        self.failure_target = failure_target
        self.mandatory = mandatory

class NetworkModel:
    def __init__(self):
        self.nodes = {}; self.edges = []

    def add_node(self, name, x, y, role='intermediate',
                 failure_target=True, mandatory=False):
        if name in self.nodes: return False
        self.nodes[name] = Node(name, x, y, role, failure_target, mandatory)
        return True

    def remove_node(self, name):
        if name not in self.nodes: return
        self.edges = [e for e in self.edges if e.src != name and e.dst != name]
        del self.nodes[name]

    def add_edge(self, src, dst, direction='atob',
                 failure_target=True, mandatory=False):
        if src not in self.nodes or dst not in self.nodes or src == dst: return False
        for e in self.edges:
            if e.src == src and e.dst == dst and e.direction == direction: return False
        self.edges.append(Edge(src, dst, direction, failure_target, mandatory))
        return True

    def remove_edge(self, eid):
        self.edges = [e for e in self.edges if e.eid != eid]

    def clear(self):
        self.nodes.clear(); self.edges.clear()

    def to_dict(self):
        return {
            'nodes': [{'name':n.name,'x':n.x,'y':n.y,'role':n.role,
                        'failure_target':n.failure_target,'mandatory':n.mandatory}
                       for n in self.nodes.values()],
            'edges': [{'src':e.src,'dst':e.dst,'direction':e.direction,
                        'failure_target':e.failure_target,'mandatory':e.mandatory}
                       for e in self.edges]}

    def from_dict(self, d):
        self.clear()
        for n in d.get('nodes',[]):
            self.add_node(n['name'],n['x'],n['y'],n.get('role','intermediate'),
                          n.get('failure_target',True), n.get('mandatory',False))
        for e in d.get('edges',[]):
            self.add_edge(e['src'],e['dst'],e.get('direction','atob'),
                          e.get('failure_target',True), e.get('mandatory',False))

class CCodeGenerator:
    def generate(self, model, output_base='result', max_rows=1000000):
        nodes = list(model.nodes.values())
        n = len(nodes)
        nmap = {nd.name: i for i, nd in enumerate(nodes)}
        sa = [nmap[nd.name] for nd in nodes if nd.role == 'source_a']
        sb = [nmap[nd.name] for nd in nodes if nd.role == 'source_b']
        edges = list(model.edges)
        return self._emit(n, nodes, nmap, sa, sb, edges, output_base, max_rows)

    def _emit(self, n, nodes, nmap, sa, sb, edges, obase, maxr):
        from collections import defaultdict
        e = len(edges)
        emap = {edge.eid: i for i, edge in enumerate(edges)}

        ft_node_idx = [i for i, nd in enumerate(nodes) if nd.failure_target]
        ft_edge_idx = [i for i, eg in enumerate(edges) if eg.failure_target]
        nfn = len(ft_node_idx)
        nfe = len(ft_edge_idx)

        mand_nodes = [i for i, nd in enumerate(nodes) if nd.mandatory]
        mand_ea = [(emap[eg.eid], nmap[eg.src], nmap[eg.dst])
                   for eg in edges if eg.mandatory and eg.direction in ('atob','both')]
        mand_eb = [(emap[eg.eid], nmap[eg.src], nmap[eg.dst])
                   for eg in edges if eg.mandatory and eg.direction in ('btoa','both')]
        mn  = len(mand_nodes)
        mna = len(mand_ea)
        mnb = len(mand_eb)

        atob_adj = defaultdict(list)
        btoa_adj = defaultdict(list)
        for edge in edges:
            s, d = nmap[edge.src], nmap[edge.dst]
            eidx = emap[edge.eid]
            if edge.direction in ('atob','both'): atob_adj[(s,d)].append(eidx)
            if edge.direction == 'btoa': btoa_adj[(s,d)].append(eidx)
            if edge.direction == 'both': btoa_adj[(d,s)].append(eidx)

        def cn(name): return name.replace('-','_').replace(' ','_')
        def edge_label(eg):
            d = {'atob':'AB','btoa':'BA','both':'BI'}[eg.direction]
            return f"{eg.src}-{eg.dst}-{d}"
        def arr(lst): return ','.join(map(str, lst))

        L = []
        L.append('#include <stdio.h>\n#include <stdlib.h>\n'
                 '#include <string.h>\n#include <stdbool.h>\n')
        L.append(f'#define NUM_NODES          {n}')
        L.append(f'#define NUM_EDGES          {e}')
        L.append(f'#define NUM_FAIL_NODES     {nfn}')
        L.append(f'#define NUM_FAIL_EDGES     {nfe}')
        L.append(f'#define NUM_COMPONENTS     (NUM_FAIL_NODES + NUM_FAIL_EDGES)')
        L.append(f'#define MAX_PATTERNS       (1L << NUM_COMPONENTS)')
        L.append(f'#define MAX_DATA_ROWS      {maxr}')
        L.append(f'#define MAX_PARALLEL       2')
        L.append(f'#define NUM_MAND_NODES     {mn}')
        L.append(f'#define NUM_MAND_EDGES_AB  {mna}')
        L.append(f'#define NUM_MAND_EDGES_BA  {mnb}\n')

        for nd in nodes: L.append(f'#define NODE_{cn(nd.name)} {nmap[nd.name]}')
        L.append('')
        L.append(f'static const int source_a[] = {{{arr(sa)}}};')
        L.append(f'#define NUM_SA {len(sa)}')
        L.append(f'static const int source_b[] = {{{arr(sb)}}};')
        L.append(f'#define NUM_SB {len(sb)}\n')

        L.append(f'static const int fail_node_idx[NUM_FAIL_NODES+1] = {{{arr(ft_node_idx)}}};')
        L.append(f'static const int fail_edge_idx[NUM_FAIL_EDGES+1] = {{{arr(ft_edge_idx)}}};\n')

        L.append(f'static const int mand_node_idx[NUM_MAND_NODES+1] = '
                 f'{{{arr(mand_nodes)}}};\n')
        if mna > 0:
            L.append(f'static const int mand_ea_eidx[NUM_MAND_EDGES_AB+1] = {{{arr([x[0] for x in mand_ea])}}};')
            L.append(f'static const int mand_ea_src [NUM_MAND_EDGES_AB+1] = {{{arr([x[1] for x in mand_ea])}}};')
            L.append(f'static const int mand_ea_dst [NUM_MAND_EDGES_AB+1] = {{{arr([x[2] for x in mand_ea])}}};\n')
        else:
            L.append('static const int mand_ea_eidx[1]={0},'
                     ' mand_ea_src[1]={0}, mand_ea_dst[1]={0};\n')
        if mnb > 0:
            L.append(f'static const int mand_eb_eidx[NUM_MAND_EDGES_BA+1] = {{{arr([x[0] for x in mand_eb])}}};')
            L.append(f'static const int mand_eb_src [NUM_MAND_EDGES_BA+1] = {{{arr([x[1] for x in mand_eb])}}};')
            L.append(f'static const int mand_eb_dst [NUM_MAND_EDGES_BA+1] = {{{arr([x[2] for x in mand_eb])}}};\n')
        else:
            L.append('static const int mand_eb_eidx[1]={0},'
                     ' mand_eb_src[1]={0}, mand_eb_dst[1]={0};\n')

        L.append('static const char *node_names[NUM_NODES] = {')
        for nd in nodes: L.append(f'    [{nmap[nd.name]}] = "{nd.name}",')
        L.append('};\n')
        if e > 0:
            L.append('static const char *edge_names[NUM_EDGES] = {')
            for i, eg in enumerate(edges): L.append(f'    [{i}] = "{edge_label(eg)}",')
            L.append('};\n')
        else:
            L.append('static const char *edge_names[1] = {""};\n')

        L.append('static int atob_edge_list[NUM_NODES][NUM_NODES][MAX_PARALLEL];')
        L.append('static int atob_edge_cnt [NUM_NODES][NUM_NODES];')
        L.append('static int btoa_edge_list[NUM_NODES][NUM_NODES][MAX_PARALLEL];')
        L.append('static int btoa_edge_cnt [NUM_NODES][NUM_NODES];\n')
        L.append('static void init_adjacency(void) {')
        L.append('    memset(atob_edge_list,-1,sizeof(atob_edge_list));')
        L.append('    memset(atob_edge_cnt, 0,sizeof(atob_edge_cnt));')
        L.append('    memset(btoa_edge_list,-1,sizeof(btoa_edge_list));')
        L.append('    memset(btoa_edge_cnt, 0,sizeof(btoa_edge_cnt));')
        for (s,d),eidxs in atob_adj.items():
            for eidx in eidxs:
                L.append(f'    if(atob_edge_cnt[{s}][{d}]<MAX_PARALLEL)'
                         f' atob_edge_list[{s}][{d}][atob_edge_cnt[{s}][{d}]++]={eidx};')
        for (s,d),eidxs in btoa_adj.items():
            for eidx in eidxs:
                L.append(f'    if(btoa_edge_cnt[{s}][{d}]<MAX_PARALLEL)'
                         f' btoa_edge_list[{s}][{d}][btoa_edge_cnt[{s}][{d}]++]={eidx};')
        L.append('}\n')

        L.append(r'''static inline int popcount(long p) { return __builtin_popcountl(p); }

static bool dfs_atob(const bool fn[NUM_NODES], const bool fe[],
                     int start, const int goals[], int ng) {
    if (fn[start]) return false;
    bool vis[NUM_NODES] = {false};
    bool in_stk[NUM_NODES] = {false};
    int stk[NUM_NODES], sp = 0;
    stk[sp++] = start; in_stk[start] = true;
    while (sp > 0) {
        int c = stk[--sp];
        if (vis[c] || fn[c]) continue;
        vis[c] = true;
        for (int g = 0; g < ng; g++) if (c == goals[g]) return true;
        for (int i = 0; i < NUM_NODES; i++) {
            if (fn[i] || vis[i] || in_stk[i] || atob_edge_cnt[c][i]==0) continue;
            bool ok = false;
            for (int k = 0; k < atob_edge_cnt[c][i]; k++)
                if (!fe[atob_edge_list[c][i][k]]) { ok=true; break; }
            if (ok) { stk[sp++] = i; in_stk[i] = true; }
        }
    }
    return false;
}

static bool dfs_btoa(const bool fn[NUM_NODES], const bool fe[],
                     int start, const int goals[], int ng) {
    if (fn[start]) return false;
    bool vis[NUM_NODES] = {false};
    bool in_stk[NUM_NODES] = {false};
    int stk[NUM_NODES], sp = 0;
    stk[sp++] = start; in_stk[start] = true;
    while (sp > 0) {
        int c = stk[--sp];
        if (vis[c] || fn[c]) continue;
        vis[c] = true;
        for (int g = 0; g < ng; g++) if (c == goals[g]) return true;
        for (int i = 0; i < NUM_NODES; i++) {
            if (fn[i] || vis[i] || in_stk[i] || btoa_edge_cnt[c][i]==0) continue;
            bool ok = false;
            for (int k = 0; k < btoa_edge_cnt[c][i]; k++)
                if (!fe[btoa_edge_list[c][i][k]]) { ok=true; break; }
            if (ok) { stk[sp++] = i; in_stk[i] = true; }
        }
    }
    return false;
}
''')

        L.append('static bool reachable_AtoB(const bool fn[], const bool fe[]) {')
        L.append('    /* 1. Basic: at least one SA can reach some SB */')
        L.append('    bool found = false;')
        L.append('    for (int i=0;i<NUM_SA;i++)')
        L.append('        if (dfs_atob(fn,fe,source_a[i],source_b,NUM_SB)) { found=true; break; }')
        L.append('    if (!found) return false;\n')
        L.append('    /* 2. Each mandatory node must lie on some SA->SB path (sandwich check) */')
        L.append('    for (int j=0;j<NUM_MAND_NODES;j++) {')
        L.append('        int m = mand_node_idx[j];')
        L.append('        if (fn[m]) return false;')
        L.append('        bool ok=false;')
        L.append('        for (int i=0;i<NUM_SA;i++)')
        L.append('            if (dfs_atob(fn,fe,source_a[i],(int[]){m},1)) { ok=true; break; }')
        L.append('        if (!ok) return false;')
        L.append('        if (!dfs_atob(fn,fe,m,source_b,NUM_SB)) return false;')
        L.append('    }\n')
        L.append('    /* 3. Each mandatory AtoB edge must be traversable and on the path */')
        L.append('    for (int j=0;j<NUM_MAND_EDGES_AB;j++) {')
        L.append('        if (fe[mand_ea_eidx[j]]) return false;')
        L.append('        int u=mand_ea_src[j], v=mand_ea_dst[j];')
        L.append('        bool ok=false;')
        L.append('        for (int i=0;i<NUM_SA;i++)')
        L.append('            if (dfs_atob(fn,fe,source_a[i],(int[]){u},1)) { ok=true; break; }')
        L.append('        if (!ok) return false;')
        L.append('        if (!dfs_atob(fn,fe,v,source_b,NUM_SB)) return false;')
        L.append('    }')
        L.append('    return true;')
        L.append('}\n')

        L.append('static bool reachable_BtoA(const bool fn[], const bool fe[]) {')
        L.append('    bool found = false;')
        L.append('    for (int i=0;i<NUM_SB;i++)')
        L.append('        if (dfs_btoa(fn,fe,source_b[i],source_a,NUM_SA)) { found=true; break; }')
        L.append('    if (!found) return false;\n')
        L.append('    for (int j=0;j<NUM_MAND_NODES;j++) {')
        L.append('        int m = mand_node_idx[j];')
        L.append('        if (fn[m]) return false;')
        L.append('        bool ok=false;')
        L.append('        for (int i=0;i<NUM_SB;i++)')
        L.append('            if (dfs_btoa(fn,fe,source_b[i],(int[]){m},1)) { ok=true; break; }')
        L.append('        if (!ok) return false;')
        L.append('        if (!dfs_btoa(fn,fe,m,source_a,NUM_SA)) return false;')
        L.append('    }\n')
        L.append('    for (int j=0;j<NUM_MAND_EDGES_BA;j++) {')
        L.append('        if (fe[mand_eb_eidx[j]]) return false;')
        L.append('        int u=mand_eb_src[j], v=mand_eb_dst[j];')
        L.append('        bool ok=false;')
        L.append('        for (int i=0;i<NUM_SB;i++)')
        L.append('            if (dfs_btoa(fn,fe,source_b[i],(int[]){u},1)) { ok=true; break; }')
        L.append('        if (!ok) return false;')
        L.append('        if (!dfs_btoa(fn,fe,v,source_a,NUM_SA)) return false;')
        L.append('    }')
        L.append('    return true;')
        L.append('}\n')

        L.append(r'''static void set_fail(long p, bool fn[NUM_NODES], bool fe[]) {
    memset(fn, 0, NUM_NODES * sizeof(bool));
    for (int i=0;i<NUM_FAIL_NODES;i++) fn[fail_node_idx[i]] = (p>>i)&1;
    for (int i=0;i<NUM_FAIL_EDGES;i++) fe[fail_edge_idx[i]] = (p>>(NUM_FAIL_NODES+i))&1;
}
static void csv_hdr(FILE *fp) {
    fprintf(fp,"failure_count");
    for (int i=0;i<NUM_NODES;i++) fprintf(fp,",%s",node_names[i]);
    for (int i=0;i<NUM_EDGES;i++) fprintf(fp,",%s",edge_names[i]);
    fprintf(fp,"\n");
}
static void csv_row(FILE *fp,int fc,const bool fn[NUM_NODES],const bool fe[]) {
    fprintf(fp,"%d",fc);
    for (int i=0;i<NUM_NODES;i++) fprintf(fp,",%s",fn[i]?"F":"T");
    for (int i=0;i<NUM_EDGES;i++) fprintf(fp,",%s",fe[i]?"F":"T");
    fprintf(fp,"\n");
}
static FILE *next_csv(const char *base,int num,char *buf,size_t len) {
    snprintf(buf,len,"%s_%d.csv",base,num);
    FILE *fp=fopen(buf,"w");
    if (fp) csv_hdr(fp);
    return fp;
}
''')

        L.append('int main(int argc, char *argv[]) {')
        L.append(f'    const char *base=(argc>=2)?argv[1]:"{obase}";')
        L.append('    init_adjacency();')
        L.append('    bool fn[NUM_NODES];')
        L.append('    bool fe[NUM_EDGES+1]; memset(fe,0,sizeof(fe));')
        L.append('    int cf=1; long rows=0,total=0; char buf[256];')
        L.append('    long unreachable_per_tc[NUM_COMPONENTS+1];')
        L.append('    long total_per_tc[NUM_COMPONENTS+1];')
        L.append('    memset(unreachable_per_tc,0,sizeof(unreachable_per_tc));')
        L.append('    memset(total_per_tc,0,sizeof(total_per_tc));')
        L.append('    FILE *fp=next_csv(base,cf,buf,sizeof(buf));')
        L.append('    if(!fp){fprintf(stderr,"Cannot open\\n");return 1;}')
        L.append('    for(int tc=0;tc<=NUM_COMPONENTS;tc++){')
        L.append('        long cnt=0,tc_total=0;')
        L.append('        for(long p=0;p<MAX_PATTERNS;p++){')
        L.append('            if(popcount(p)!=tc) continue;')
        L.append('            tc_total++;')
        L.append('            set_fail(p,fn,fe);')
        L.append('            if(reachable_AtoB(fn,fe)) continue;')
        L.append('            if(reachable_BtoA(fn,fe)) continue;')
        L.append('            csv_row(fp,tc,fn,fe); rows++; cnt++;')
        L.append('            if(rows>=MAX_DATA_ROWS){')
        L.append('                fclose(fp); cf++;')
        L.append('                fp=next_csv(base,cf,buf,sizeof(buf));')
        L.append('                if(!fp){fprintf(stderr,"Cannot open\\n");return 1;}')
        L.append('                rows=0;}')
        L.append('        }')
        L.append('        unreachable_per_tc[tc]=cnt;')
        L.append('        total_per_tc[tc]=tc_total;')
        L.append('        printf("Failures %2d: unreachable=%ld  reachable=%ld  total=%ld\\n",'
                 'tc,cnt,tc_total-cnt,tc_total);')
        L.append('        total+=cnt;')
        L.append('    }')
        L.append('    fclose(fp);')
        L.append('    char sum_fn[256];')
        L.append('    snprintf(sum_fn,sizeof(sum_fn),"%s_summary.csv",base);')
        L.append('    FILE *sfp=fopen(sum_fn,"w");')
        L.append('    if(!sfp){fprintf(stderr,"Cannot open summary\\n");return 1;}')
        L.append('    fprintf(sfp,"failure_count,unreachable_count,reachable_count,total_count,arrival_rate\\n");')
        L.append('    for(int tc=0;tc<=NUM_COMPONENTS;tc++){')
        L.append('        long reach=total_per_tc[tc]-unreachable_per_tc[tc];')
        L.append('        double rate=total_per_tc[tc]>0?(double)reach/total_per_tc[tc]:0.0;')
        L.append('        fprintf(sfp,"%d,%ld,%ld,%ld,%.6f\\n",tc,unreachable_per_tc[tc],reach,total_per_tc[tc],rate);')
        L.append('    }')
        L.append('    fclose(sfp);')
        L.append('    printf("-----------------------------\\n");')
        L.append('    printf("Total unreachable: %ld patterns / %d detail files\\n",total,cf);')
        L.append('    printf("Summary: %s\\n",sum_fn);')
        L.append('    return 0;')
        L.append('}')
        return '\n'.join(L)

def make_preset_24():
    """24-node configuration with cross paths"""
    ns = [
        ('A1',80,180,'source_a'),('A2',80,520,'source_a'),
        ('ERP1_1',380,150,'intermediate'),('ERP1_2',660,100,'intermediate'),
        ('ERP1_3',660,230,'intermediate'),
        ('ERP2_1',380,550,'intermediate'),('ERP2_2',660,470,'intermediate'),
        ('ERP2_3',660,600,'intermediate'),
        ('B1',1050,180,'source_b'),('B2',1050,520,'source_b'),
        ('L_A1_ERP1_1',220,120,'intermediate'),('L_A1_ERP2_1',220,310,'intermediate'),
        ('L_A2_ERP1_1',220,390,'intermediate'),('L_A2_ERP2_1',220,580,'intermediate'),
        ('L_ERP1_1_ERP1_2',520,100,'intermediate'),('L_ERP1_1_ERP1_3',520,210,'intermediate'),
        ('L_ERP1_2_B1',830,100,'intermediate'),('L_ERP1_3_ERP1_2',580,170,'intermediate'),
        ('L_ERP2_1_ERP2_2',520,490,'intermediate'),('L_ERP2_1_ERP2_3',520,590,'intermediate'),
        ('L_ERP2_2_B2',830,470,'intermediate'),('L_ERP2_3_ERP2_2',580,540,'intermediate'),
        ('L_ERP1_2_B2',870,310,'intermediate'),('L_ERP2_2_B1',870,380,'intermediate'),
    ]
    ea = [
        ('A1','L_A1_ERP1_1'),('L_A1_ERP1_1','ERP1_1'),
        ('A1','L_A1_ERP2_1'),('L_A1_ERP2_1','ERP2_1'),
        ('A2','L_A2_ERP1_1'),('L_A2_ERP1_1','ERP1_1'),
        ('A2','L_A2_ERP2_1'),('L_A2_ERP2_1','ERP2_1'),
        ('ERP1_1','L_ERP1_1_ERP1_2'),('L_ERP1_1_ERP1_2','ERP1_2'),
        ('ERP1_1','L_ERP1_1_ERP1_3'),('L_ERP1_1_ERP1_3','ERP1_3'),
        ('ERP1_2','L_ERP1_2_B1'),('L_ERP1_2_B1','B1'),
        ('ERP1_3','L_ERP1_3_ERP1_2'),('L_ERP1_3_ERP1_2','ERP1_2'),
        ('ERP2_1','L_ERP2_1_ERP2_2'),('L_ERP2_1_ERP2_2','ERP2_2'),
        ('ERP2_1','L_ERP2_1_ERP2_3'),('L_ERP2_1_ERP2_3','ERP2_3'),
        ('ERP2_2','L_ERP2_2_B2'),('L_ERP2_2_B2','B2'),
        ('ERP2_3','L_ERP2_3_ERP2_2'),('L_ERP2_3_ERP2_2','ERP2_2'),
        ('ERP1_2','L_ERP1_2_B2'),('L_ERP1_2_B2','B2'),
        ('ERP2_2','L_ERP2_2_B1'),('L_ERP2_2_B1','B1'),
    ]
    eb = [
        ('B1','L_ERP1_2_B1'),('L_ERP1_2_B1','ERP1_2'),
        ('B2','L_ERP2_2_B2'),('L_ERP2_2_B2','ERP2_2'),
        ('ERP1_2','L_ERP1_1_ERP1_2'),('L_ERP1_1_ERP1_2','ERP1_1'),
        ('ERP1_2','L_ERP1_3_ERP1_2'),('L_ERP1_3_ERP1_2','ERP1_3'),
        ('ERP1_3','L_ERP1_1_ERP1_3'),('L_ERP1_1_ERP1_3','ERP1_1'),
        ('ERP1_1','L_A1_ERP1_1'),('L_A1_ERP1_1','A1'),
        ('ERP1_1','L_A2_ERP1_1'),('L_A2_ERP1_1','A2'),
        ('ERP2_2','L_ERP2_1_ERP2_2'),('L_ERP2_1_ERP2_2','ERP2_1'),
        ('ERP2_2','L_ERP2_3_ERP2_2'),('L_ERP2_3_ERP2_2','ERP2_3'),
        ('ERP2_3','L_ERP2_1_ERP2_3'),('L_ERP2_1_ERP2_3','ERP2_1'),
        ('ERP2_1','L_A1_ERP2_1'),('L_A1_ERP2_1','A1'),
        ('ERP2_1','L_A2_ERP2_1'),('L_A2_ERP2_1','A2'),
        ('B2','L_ERP1_2_B2'),('L_ERP1_2_B2','ERP1_2'),
        ('B1','L_ERP2_2_B1'),('L_ERP2_2_B1','ERP2_2'),
    ]
    d = {'nodes':[{'name':nm,'x':x,'y':y,'role':r} for nm,x,y,r in ns], 'edges':[]}
    for s,t in ea: d['edges'].append({'src':s,'dst':t,'direction':'atob'})
    for s,t in eb: d['edges'].append({'src':s,'dst':t,'direction':'btoa'})
    return d

class App:
    def __init__(self, root):
        self.root = root
        self.root.title("Network Reachability Analyzer")
        self.root.geometry("1280x820")
        self.model = NetworkModel()
        self.mode = 'select'
        self.selected = None
        self.edge_src = None
        self.dragging = None
        self.drag_offset = (0, 0)
        self.canvas_ids = {}
        self.node_items = {}
        self.edge_items = {}
        self.edge_offsets = {}
        self._build_ui()

    def _build_ui(self):
        tb = ttk.Frame(self.root); tb.pack(fill=tk.X, padx=4, pady=2)
        ttk.Label(tb, text="Mode:").pack(side=tk.LEFT, padx=(4,2))
        self.mode_var = tk.StringVar(value='select')
        modes = [('Select/Move','select'),('Add Node','add_node'),
                 ('Edge(A->B)','add_edge_atob'),('Edge(B->A)','add_edge_btoa'),
                 ('Edge(Both)','add_edge_both'),('Delete','delete'),
                 ('Toggle Fail','toggle_fail'),('Toggle Mandatory','toggle_mandatory')]
        for txt, val in modes:
            ttk.Radiobutton(tb, text=txt, variable=self.mode_var, value=val,
                            command=self._mode_changed).pack(side=tk.LEFT, padx=2)

        ttk.Separator(tb, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=6)
        ttk.Label(tb, text="Node Role:").pack(side=tk.LEFT, padx=2)
        self.role_var = tk.StringVar(value='intermediate')
        for txt, val in [('Source A','source_a'),('Source B','source_b'),('Intermediate','intermediate')]:
            ttk.Radiobutton(tb, text=txt, variable=self.role_var, value=val).pack(side=tk.LEFT, padx=1)

        ttk.Separator(tb, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=6)
        ttk.Button(tb, text="Run Analysis",  command=self._run_analysis).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="Reliability",   command=self._run_reliability).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="Export C",      command=self._export_c).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="Save",         command=self._save).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="Load",         command=self._load).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="Preset",       command=self._load_preset).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="Clear",        command=self._clear).pack(side=tk.LEFT, padx=2)

        pw = ttk.PanedWindow(self.root, orient=tk.VERTICAL)
        pw.pack(fill=tk.BOTH, expand=True, padx=4, pady=2)

        cf = ttk.Frame(pw)
        self.canvas = tk.Canvas(cf, bg=COLORS['canvas_bg'], width=1200, height=500,
                                scrollregion=(0,0,2000,1200))
        sx = ttk.Scrollbar(cf, orient=tk.HORIZONTAL, command=self.canvas.xview)
        sy = ttk.Scrollbar(cf, orient=tk.VERTICAL,   command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=sx.set, yscrollcommand=sy.set)
        sy.pack(side=tk.RIGHT, fill=tk.Y); sx.pack(side=tk.BOTTOM, fill=tk.X)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        pw.add(cf, weight=3)

        rf = ttk.LabelFrame(pw, text="Analysis Results")
        self.result_text = scrolledtext.ScrolledText(rf, height=10, font=('Consolas',10))
        self.result_text.pack(fill=tk.BOTH, expand=True)
        pw.add(rf, weight=1)

        self.status_var = tk.StringVar(value="Mode: Select/Move")
        ttk.Label(self.root, textvariable=self.status_var, relief=tk.SUNKEN,
                  anchor=tk.W).pack(fill=tk.X, side=tk.BOTTOM)

        self.canvas.bind('<Button-1>',       self._on_click)
        self.canvas.bind('<B1-Motion>',      self._on_drag)
        self.canvas.bind('<ButtonRelease-1>',self._on_release)
        self.root.bind('<Delete>',           self._on_delete_key)
        self.root.bind('<Escape>',           self._on_escape)
        self._draw_grid()

    def _mode_changed(self):
        self.mode = self.mode_var.get()
        self.edge_src = None
        labels = {
            'select':           'Select/Move',
            'add_node':         'Add Node (click on canvas)',
            'add_edge_atob':    'Edge(A->B): click source node',
            'add_edge_btoa':    'Edge(B->A): click source node',
            'add_edge_both':    'Edge(Both): click source node',
            'delete':           'Click node/edge to delete',
            'toggle_fail':      'Click node/edge to toggle failure target '
                                '(solid outline = target, dashed = excluded)',
            'toggle_mandatory': 'Click node/edge to toggle mandatory '
                                '(gold ring = must be on path)',
        }
        self.status_var.set(f"Mode: {labels.get(self.mode, self.mode)}")
        self._redraw()

    def _redraw(self):
        self.canvas.delete('dynamic')
        self.canvas_ids.clear()
        self.node_items.clear()
        self.edge_items.clear()
        self.edge_offsets = self._compute_edge_offsets()
        for e in self.model.edges:
            self._draw_edge(e, self.edge_offsets.get(e.eid, 0))
        for nd in self.model.nodes.values():
            self._draw_node(nd)
        if self.edge_src and self.edge_src in self.model.nodes:
            nd = self.model.nodes[self.edge_src]
            self.canvas.create_oval(nd.x-NODE_R-4, nd.y-NODE_R-4,
                                    nd.x+NODE_R+4, nd.y+NODE_R+4,
                                    outline=COLORS['select'], width=3,
                                    dash=(4,2), tags='dynamic')

    def _draw_grid(self):
        for x in range(0, 2001, 50):
            self.canvas.create_line(x,0,x,1200, fill=COLORS['grid'], width=1, tags='grid')
        for y in range(0, 1201, 50):
            self.canvas.create_line(0,y,2000,y, fill=COLORS['grid'], width=1, tags='grid')

    def _draw_node(self, node):
        x, y, r = node.x, node.y, NODE_R
        col = COLORS.get(node.role, COLORS['intermediate'])
        sel = self.selected == ('node', node.name)
        ow = 3 if sel else 1.5
        oc = COLORS['select'] if sel else '#1E293B'
        dash = (5,4) if not node.failure_target else ()
        cid = self.canvas.create_oval(x-r, y-r, x+r, y+r, fill=col, outline=oc,
                                      width=ow, dash=dash, tags='dynamic')
        self.canvas_ids[cid] = ('node', node.name)
        fs = 8 if len(node.name) > 6 else 9
        tid = self.canvas.create_text(x, y+r+10, text=node.name, font=('Arial',fs),
                                      fill='#1E293B', anchor=tk.N, tags='dynamic')
        self.canvas_ids[tid] = ('node', node.name)
        items = [cid, tid]
        if node.role != 'intermediate':
            badge = 'A' if node.role == 'source_a' else 'B'
            bid = self.canvas.create_text(x, y, text=badge, fill='white',
                                          font=('Arial',10,'bold'), tags='dynamic')
            items.append(bid)
        if not node.failure_target:
            xid = self.canvas.create_text(x+r-4, y-r+4, text='x', fill='white',
                                           font=('Arial',7,'bold'), tags='dynamic')
            items.append(xid)
        if node.mandatory:
            mid = self.canvas.create_oval(x-r-5, y-r-5, x+r+5, y+r+5,
                                          outline=COLORS['mandatory'], width=2.5,
                                          tags='dynamic')
            mid2 = self.canvas.create_text(x+r+1, y-r-1, text='M', fill=COLORS['mandatory'],
                                            font=('Arial',7,'bold'), tags='dynamic')
            items += [mid, mid2]
        self.node_items[node.name] = items

    def _compute_edge_offsets(self):
        groups = {}
        for e in self.model.edges:
            key = (min(e.src,e.dst), max(e.src,e.dst))
            groups.setdefault(key,[]).append(e)
        offsets = {}
        for group in groups.values():
            n = len(group)
            for i, e in enumerate(group):
                offsets[e.eid] = (i-(n-1)/2)*8 if n > 1 else 0
        return offsets

    def _calc_edge_coords(self, edge, offset):
        if edge.src not in self.model.nodes or edge.dst not in self.model.nodes:
            return None
        ns, nd = self.model.nodes[edge.src], self.model.nodes[edge.dst]
        dx, dy = nd.x-ns.x, nd.y-ns.y
        dist = math.sqrt(dx*dx+dy*dy)
        if dist < 1: return None
        ux, uy = dx/dist, dy/dist
        x1, y1 = ns.x+ux*NODE_R, ns.y+uy*NODE_R
        x2, y2 = nd.x-ux*NODE_R, nd.y-uy*NODE_R
        if offset != 0:
            px, py = -uy*offset, ux*offset
            x1+=px; y1+=py; x2+=px; y2+=py
        return x1, y1, x2, y2

    def _draw_edge(self, edge, offset=0):
        coords = self._calc_edge_coords(edge, offset)
        if coords is None: return
        x1, y1, x2, y2 = coords
        col = COLORS.get(f'edge_{edge.direction}', COLORS['edge_atob'])
        sel = self.selected == ('edge', edge.eid)
        w = 3 if sel else 1.5
        if sel: col = COLORS['select']
        dash = (8,5) if not edge.failure_target else ()
        cid = self.canvas.create_line(x1,y1,x2,y2, fill=col, width=w,
                                      arrow=tk.LAST, arrowshape=(10,12,5),
                                      dash=dash, tags='dynamic')
        self.canvas_ids[cid] = ('edge', edge.eid)
        self.edge_items[edge.eid] = cid
        if edge.mandatory:
            mx, my = (x1+x2)/2, (y1+y2)/2
            r = 5
            mid = self.canvas.create_polygon(mx,my-r, mx+r,my, mx,my+r, mx-r,my,
                                              fill=COLORS['mandatory'], outline='',
                                              tags='dynamic')
            self.canvas_ids[mid] = ('edge', edge.eid)

    def _update_edge_coords(self, edge):
        cid = self.edge_items.get(edge.eid)
        if cid is None: return
        coords = self._calc_edge_coords(edge, self.edge_offsets.get(edge.eid,0))
        if coords is None: return
        self.canvas.coords(cid, *coords)

    def _find_item(self, x, y):
        items = self.canvas.find_overlapping(x-5,y-5,x+5,y+5)
        for item in reversed(items):
            if item in self.canvas_ids: return self.canvas_ids[item]
        return None

    def _on_click(self, event):
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        item = self._find_item(x, y)

        if self.mode == 'select':
            self.selected = item
            if item and item[0] == 'node':
                self.dragging = item[1]
                nd = self.model.nodes[self.dragging]
                self.drag_offset = (x-nd.x, y-nd.y)
            self._redraw()

        elif self.mode == 'add_node':
            name = simpledialog.askstring("Add Node", "Node name:", parent=self.root)
            if name and name.strip():
                name = name.strip()
                if self.model.add_node(name, x, y, self.role_var.get()):
                    self._redraw()
                else:
                    messagebox.showwarning("Warning", f"Node '{name}' already exists")

        elif self.mode.startswith('add_edge'):
            if item and item[0] == 'node':
                if self.edge_src is None:
                    self.edge_src = item[1]
                    self.status_var.set(f"Source: {item[1]} -> click destination node")
                    self._redraw()
                else:
                    direction = self.mode.replace('add_edge_','')
                    if self.model.add_edge(self.edge_src, item[1], direction):
                        self.edge_src = None; self._mode_changed(); self._redraw()
                    else:
                        messagebox.showwarning("Warning","Cannot add edge (duplicate or self-loop)")
                        self.edge_src = None; self._mode_changed()

        elif self.mode == 'delete':
            if item:
                if item[0] == 'node': self.model.remove_node(item[1])
                elif item[0] == 'edge': self.model.remove_edge(item[1])
                self.selected = None; self._redraw()

        elif self.mode == 'toggle_fail':
            if item:
                if item[0] == 'node':
                    self.model.nodes[item[1]].failure_target ^= True
                elif item[0] == 'edge':
                    for eg in self.model.edges:
                        if eg.eid == item[1]: eg.failure_target ^= True; break
                self._redraw()

        elif self.mode == 'toggle_mandatory':
            if item:
                if item[0] == 'node':
                    self.model.nodes[item[1]].mandatory ^= True
                elif item[0] == 'edge':
                    for eg in self.model.edges:
                        if eg.eid == item[1]: eg.mandatory ^= True; break
                self._redraw()

    def _on_drag(self, event):
        if self.mode == 'select' and self.dragging:
            node = self.model.nodes[self.dragging]
            new_x = self.canvas.canvasx(event.x) - self.drag_offset[0]
            new_y = self.canvas.canvasy(event.y) - self.drag_offset[1]
            dx, dy = new_x-node.x, new_y-node.y
            node.x, node.y = new_x, new_y
            for cid in self.node_items.get(self.dragging,[]):
                self.canvas.move(cid, dx, dy)
            for e in self.model.edges:
                if e.src == self.dragging or e.dst == self.dragging:
                    self._update_edge_coords(e)

    def _on_release(self, event): self.dragging = None

    def _on_delete_key(self, event):
        if self.selected:
            if self.selected[0] == 'node': self.model.remove_node(self.selected[1])
            elif self.selected[0] == 'edge': self.model.remove_edge(self.selected[1])
            self.selected = None; self._redraw()

    def _on_escape(self, event):
        self.edge_src = None; self.selected = None
        self.mode_var.set('select'); self._mode_changed()

    def _run_analysis(self):
        n = len(self.model.nodes)
        if n == 0:
            messagebox.showwarning("Warning","No nodes defined"); return
        sa = [nd for nd in self.model.nodes.values() if nd.role == 'source_a']
        sb = [nd for nd in self.model.nodes.values() if nd.role == 'source_b']
        if not sa or not sb:
            messagebox.showwarning("Warning","Please set both Source A and Source B nodes"); return

        ft_nodes = sum(1 for nd in self.model.nodes.values() if nd.failure_target)
        ft_edges = sum(1 for eg in self.model.edges if eg.failure_target)
        nc = ft_nodes + ft_edges
        if nc == 0:
            messagebox.showwarning("Warning",
                "No failure targets selected.\n"
                "Mark at least one node or edge as a failure target."); return
        if nc > 28:
            messagebox.showwarning("Warning",
                f"Too many failure targets ({ft_nodes} nodes + {ft_edges} edges = {nc}). "
                "Maximum is 28."); return

        mand_n = sum(1 for nd in self.model.nodes.values() if nd.mandatory)
        mand_e = sum(1 for eg in self.model.edges if eg.mandatory)

        gcc = shutil.which('gcc')
        if not gcc:
            messagebox.showerror("Error","gcc not found.\nPlease add gcc to your PATH.")
            return

        outdir = filedialog.askdirectory(title="Select Output Folder")
        if not outdir: return

        self.result_text.delete('1.0', tk.END)
        self.result_text.insert(tk.END,
            f"Starting analysis...\n"
            f"  Failure targets : {ft_nodes} nodes + {ft_edges} edges = {nc} components\n"
            f"  Mandatory       : {mand_n} nodes + {mand_e} edges\n"
            f"  Patterns        : 2^{nc} = {2**nc:,}\n")
        self.result_text.insert(tk.END, "Generating C code and compiling...\n")
        self.result_text.update()

        def worker():
            try:
                gen = CCodeGenerator()
                code = gen.generate(self.model, output_base=os.path.join(outdir,'result'))
                c_path = os.path.join(outdir,'analyzer.c')
                with open(c_path,'w',encoding='utf-8') as f: f.write(code)
                self._log(f"C code written: {c_path}\n")
                exe = os.path.join(outdir,'analyzer.exe' if sys.platform=='win32' else 'analyzer')
                proc = subprocess.run([gcc,'-O2','-o',exe,c_path],
                                      capture_output=True, text=True)
                if proc.returncode != 0:
                    self._log(f"Compile error:\n{proc.stderr}\n"); return
                self._log("Compile succeeded. Running...\n")
                proc = subprocess.Popen([exe], stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, text=True, cwd=outdir)
                for line in proc.stdout: self._log(line)
                proc.wait()
                if proc.returncode != 0:
                    self._log(f"Runtime error:\n{proc.stderr.read()}\n")
                else:
                    self._log("\nAnalysis complete.\n")
                    csvs = sorted([f for f in os.listdir(outdir)
                                   if f.startswith('result_') and f.endswith('.csv')])
                    if csvs:
                        self._log(f"Output files ({len(csvs)}):\n")
                        for fn in csvs:
                            sz = os.path.getsize(os.path.join(outdir,fn))
                            self._log(f"  {fn} ({sz/1024/1024:.1f} MB)\n")
                    self._generate_graph(outdir)
                    self._analyze_reliability(outdir)
            except Exception as ex:
                self._log(f"Error: {ex}\n")

        threading.Thread(target=worker, daemon=True).start()

    def _log(self, text):
        self.root.after(0, lambda: (self.result_text.insert(tk.END, text),
                                    self.result_text.see(tk.END)))

    def _generate_graph(self, outdir):
        import csv
        summary_path = os.path.join(outdir, 'result_summary.csv')
        if not os.path.exists(summary_path):
            self._log("Summary CSV not found; skipping graph.\n")
            return

        failure_counts, arrival_rates = [], []
        try:
            with open(summary_path, newline='', encoding='utf-8') as f:
                for row in csv.DictReader(f):
                    tc = int(row['failure_count'])
                    rate = float(row['arrival_rate'])
                    failure_counts.append(tc)
                    arrival_rates.append(rate)
        except Exception as ex:
            self._log(f"Failed to read summary CSV: {ex}\n")
            return

        try:
            import matplotlib
            matplotlib.use('Agg')
            import matplotlib.pyplot as plt
            import matplotlib.ticker as mticker

            fig, ax = plt.subplots(figsize=(10, 5))
            ax.plot(failure_counts, [r * 100 for r in arrival_rates],
                    'b-o', markersize=5, linewidth=2, label='Arrival Rate')
            ax.fill_between(failure_counts, [r * 100 for r in arrival_rates],
                            alpha=0.15, color='blue')
            ax.set_xlabel('Number of Failures', fontsize=12)
            ax.set_ylabel('Arrival Rate (%)', fontsize=12)
            ax.set_title('Message Arrival Rate vs Failure Count', fontsize=14)
            ax.set_ylim(0, 105)
            ax.yaxis.set_major_formatter(mticker.FormatStrFormatter('%.0f%%'))
            ax.grid(True, alpha=0.4)
            ax.legend()
            plt.tight_layout()
            png_path = os.path.join(outdir, 'result_graph.png')
            plt.savefig(png_path, dpi=150, bbox_inches='tight')
            plt.close()
            self._log(f"Graph PNG : {png_path}\n")
        except ImportError:
            self._log("matplotlib not installed; PNG graph skipped.\n"
                      "  Install with: pip install matplotlib\n")
        except Exception as ex:
            self._log(f"Graph PNG error: {ex}\n")

    def _run_reliability(self):
        outdir = filedialog.askdirectory(title="Select Output Folder")
        if not outdir:
            return
        self.result_text.delete('1.0', tk.END)
        threading.Thread(
            target=self._analyze_reliability, args=(outdir,), daemon=True
        ).start()

    def _analyze_reliability(self, outdir):
        import csv as csv_mod

        detail_csvs = sorted(
            [f for f in os.listdir(outdir)
             if f.startswith('result_') and f.endswith('.csv')
             and 'summary' not in f and 'reliability' not in f],
            key=lambda name: int(name[len('result_'):-len('.csv')])
        )
        if not detail_csvs:
            self._log("result_*.csv not found. Please run the analysis first.\n")
            return

        first_path = os.path.join(outdir, detail_csvs[0])
        with open(first_path, newline='', encoding='utf-8') as f:
            columns = csv_mod.DictReader(f).fieldnames or []
        component_cols = [c for c in columns if c != 'failure_count']
        n = len(component_cols)
        if n == 0:
            self._log("No component columns found.\n")
            return

        half = 1 << (n - 1)

        u_fail = {c: 0 for c in component_cols}
        u_work = {c: 0 for c in component_cols}
        spof_set = set()

        self._log("Calculating SPOF and Birnbaum importance...\n")
        for fname in detail_csvs:
            with open(os.path.join(outdir, fname), newline='', encoding='utf-8') as f:
                for row in csv_mod.DictReader(f):
                    fc = int(row['failure_count'])
                    for c in component_cols:
                        if row[c] == 'F':
                            u_fail[c] += 1
                            if fc == 1:
                                spof_set.add(c)
                        else:
                            u_work[c] += 1

        birnbaum = {c: (u_fail[c] - u_work[c]) / half for c in component_cols}
        ranked = sorted(birnbaum.items(), key=lambda x: x[1], reverse=True)

        self._log("\n" + "=" * 52 + "\n")
        self._log("=== Single Points of Failure (SPOF) ===\n")
        spof_list = [c for c in component_cols if c in spof_set]
        if spof_list:
            for c in spof_list:
                self._log(f"  [SPOF] {c}\n")
        else:
            self._log("  No SPOF found\n")

        self._log("\n=== Birnbaum Importance (descending) ===\n")
        self._log(f"  {'Component':<30} {'Importance':>10}  Note\n")
        self._log(f"  {'-' * 50}\n")
        for c, imp in ranked:
            note = "  *SPOF" if c in spof_set else ""
            self._log(f"  {c:<30} {imp:>10.6f}{note}\n")
        self._log("=" * 52 + "\n")

        out_path = os.path.join(outdir, 'result_reliability.csv')
        with open(out_path, 'w', newline='', encoding='utf-8') as f:
            w = csv_mod.writer(f)
            w.writerow(['component', 'is_spof',
                        'unreachable_when_failed', 'unreachable_when_working',
                        'birnbaum_importance'])
            for c, imp in ranked:
                w.writerow([c, 'Y' if c in spof_set else 'N',
                             u_fail[c], u_work[c], f'{imp:.8f}'])
        self._log(f"Reliability analysis result saved: {out_path}\n")
        self._generate_reliability_graph(outdir, ranked, spof_set)

    def _generate_reliability_graph(self, outdir, ranked, spof_set):
        try:
            import matplotlib
            matplotlib.use('Agg')
            import matplotlib.pyplot as plt
            import matplotlib.patches as mpatches

            names  = [c   for c, _ in ranked]
            values = [imp for _, imp in ranked]
            colors = ['#EF4444' if c in spof_set else '#3B82F6' for c in names]

            fig_h = max(4, len(names) * 0.38)
            fig, axes = plt.subplots(
                1, 2,
                figsize=(14, fig_h),
                gridspec_kw={'width_ratios': [3, 1]}
            )

            ax = axes[0]
            bars = ax.barh(names, values, color=colors, edgecolor='white', height=0.7)
            ax.invert_yaxis()
            ax.axvline(0, color='#475569', linewidth=0.8, linestyle='--')
            ax.set_xlabel('Birnbaum Importance', fontsize=11)
            ax.set_title('Birnbaum Importance per Component', fontsize=13, pad=10)
            ax.grid(True, axis='x', alpha=0.3)

            x_max = max(values) if values else 1
            x_min = min(values) if values else 0
            ax.set_xlim(min(0, x_min) - 0.05, x_max + 0.15)

            fs = max(6, min(9, int(180 / max(len(names), 1))))
            for bar, val, name in zip(bars, values, names):
                ax.text(val + x_max * 0.01,
                        bar.get_y() + bar.get_height() / 2,
                        f'{val:.4f}', va='center', ha='left', fontsize=fs)
                if name in spof_set:
                    ax.text(min(0, x_min) - 0.03,
                            bar.get_y() + bar.get_height() / 2,
                            '*', va='center', ha='center',
                            color='#EF4444', fontsize=fs + 1)

            spof_patch  = mpatches.Patch(color='#EF4444', label='SPOF')
            norm_patch  = mpatches.Patch(color='#3B82F6', label='Normal')
            ax.legend(handles=[spof_patch, norm_patch], loc='lower right', fontsize=9)

            ax2 = axes[1]
            ax2.axis('off')

            spof_list = [c for c in names if c in spof_set]
            header = f"SPOF  ({len(spof_list)} / {len(names)} components)"
            lines  = [header, '-' * 28]
            if spof_list:
                lines += [f'  * {c}' for c in spof_list]
            else:
                lines.append('  (none)')

            ax2.text(0.05, 0.97, '\n'.join(lines),
                     transform=ax2.transAxes,
                     va='top', ha='left',
                     fontsize=9, fontfamily='monospace',
                     bbox=dict(boxstyle='round,pad=0.6',
                               facecolor='#FEF2F2' if spof_list else '#F0FDF4',
                               edgecolor='#EF4444' if spof_list else '#22C55E',
                               linewidth=1.5))

            plt.suptitle('Reliability Analysis', fontsize=14, y=1.01)
            plt.tight_layout()

            png_path = os.path.join(outdir, 'result_reliability_graph.png')
            plt.savefig(png_path, dpi=150, bbox_inches='tight')
            plt.close()
            self._log(f"Reliability graph saved: {png_path}\n")

        except ImportError:
            self._log("matplotlib is not installed; skipping graph.\n"
                      "  Install it with: pip install matplotlib\n")
        except Exception as ex:
            self._log(f"Reliability graph generation error: {ex}\n")

    def _export_c(self):
        if not self.model.nodes:
            messagebox.showwarning("Warning","No nodes defined"); return
        path = filedialog.asksaveasfilename(defaultextension='.c',
                                            filetypes=[('C source','*.c')])
        if not path: return
        code = CCodeGenerator().generate(self.model)
        with open(path,'w',encoding='utf-8') as f: f.write(code)
        messagebox.showinfo("Done", f"C code exported:\n{path}")

    def _save(self):
        path = filedialog.asksaveasfilename(defaultextension='.json',
                                            filetypes=[('JSON','*.json')])
        if not path: return
        with open(path,'w',encoding='utf-8') as f:
            json.dump(self.model.to_dict(), f, ensure_ascii=False, indent=2)

    def _load(self):
        path = filedialog.askopenfilename(filetypes=[('JSON','*.json')])
        if not path: return
        with open(path,'r',encoding='utf-8') as f:
            self.model.from_dict(json.load(f))
        self.selected = None; self._redraw()

    def _load_preset(self):
        if self.model.nodes:
            if not messagebox.askyesno("Confirm","Discard current topology and load preset?"):
                return
        self.model.from_dict(make_preset_24())
        self.selected = None; self._redraw()
        self.status_var.set("Loaded preset (24-node with cross paths)")

    def _clear(self):
        if self.model.nodes:
            if not messagebox.askyesno("Confirm","Clear all nodes and edges?"): return
        self.model.clear(); self.selected = None; self._redraw()

if __name__ == '__main__':
    root = tk.Tk()
    app = App(root)

    def _shutdown(sig, frame):
        root.destroy()
        sys.exit(0)

    signal.signal(signal.SIGINT,  _shutdown)
    signal.signal(signal.SIGTERM, _shutdown)
    if hasattr(signal, 'SIGTSTP'):
        signal.signal(signal.SIGTSTP, _shutdown)

    root.mainloop()
