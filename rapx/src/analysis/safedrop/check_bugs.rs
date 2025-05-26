use std::collections::{HashMap, HashSet};

use super::adg::AlarmKind;
use super::graph::*;
use crate::rap_info;
use crate::utils::source::*;
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::SourceInfo;
use rustc_span::symbol::Symbol;
use rustc_span::Span;

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn report_bugs(&self) {
        let filename = get_filename(self.tcx, self.def_id);
        match filename {
            Some(filename) => {
                if filename.contains(".cargo") {
                    return;
                }
            }
            None => {}
        }
        if self.bug_records.is_bug_free() {
            return;
        }
        let fn_name = match get_name(self.tcx, self.def_id) {
            Some(name) => name,
            None => Symbol::intern("no symbol available"),
        };
        self.bug_records.df_bugs_output(fn_name, self.span);
        self.bug_records.uaf_bugs_output(fn_name, self.span);
        self.bug_records.dp_bug_output(fn_name, self.span);
    }

    pub fn uaf_check(
        &mut self,
        aliaset_idx: usize,
        span: Span,
        local: usize,
        is_func_call: bool,
    ) -> (bool, usize) {
        let mut record = FxHashSet::default();
        if self.values[aliaset_idx].may_drop
            && (!self.values[aliaset_idx].is_ptr()
                || self.values[aliaset_idx].local != local
                || is_func_call)
            && self.exist_dead(aliaset_idx, &mut record, false)
            && !self.bug_records.uaf_bugs.contains(&span)
        {
            self.bug_records.uaf_bugs.insert(span.clone());

            rap_info!(
                "(uaf_check) aliaset_idx: {:?}, its birth: {:?}, record: {:?}",
                aliaset_idx,
                self.values[aliaset_idx].birth,
                record
            );
            if let Some(dead_node) = record.iter().find(|&&i| !self.values[i].is_alive()) {
                return (true, *dead_node);
            }

            return (true, aliaset_idx);
        }
        (false, 0)
    }

    pub fn exist_dead(
        &mut self,
        node: usize,
        record: &mut FxHashSet<usize>,
        dangling: bool,
    ) -> bool {
        if node >= self.values.len() {
            return false;
        }
        record.insert(node);
        //if is a dangling pointer check, only check the pointer type varible.
        if self.values[node].is_alive() == false
            && (dangling && self.values[node].is_ptr() || !dangling)
        {
            return true;
        }
        if self.union_has_alias(node) {
            // for i in self.values[node].alias.clone().into_iter() {
            //     if i != node && record.contains(&i) == false && self.exist_dead(i, record, dangling)
            //     {
            //         return true;
            //     }
            // }
            for i in 0..self.alias_set.len() {
                if i != node && !self.union_is_same(i, node) {
                    continue;
                }
                if record.contains(&i) == false && self.exist_dead(i, record, dangling) {
                    return true;
                }
            }
        }
        for i in self.values[node].fields.clone().into_iter() {
            if record.contains(&i.1) == false && self.exist_dead(i.1, record, dangling) {
                return true;
            }
        }
        return false;
    }

    pub fn is_dangling(&mut self, local: usize) -> (bool, usize) {
        let mut record = FxHashSet::default();
        let res = self.exist_dead(local, &mut record, local != 0);

        if res {
            if let Some(dead_node) = record.iter().find(|&&i| !self.values[i].is_alive()) {
                return (true, *dead_node);
            }
            return (true, local);
        }
        return (false, 0);
    }

    pub fn df_check(&mut self, drop: usize, span: Span) -> bool {
        let root = self.values[drop].local;
        if self.values[drop].is_alive() == false
            && self.bug_records.df_bugs.contains_key(&root) == false
        {
            self.bug_records.df_bugs.insert(root, span.clone());

            if let Some(drop_before_id) = self.adg.get_drop_node(drop) {
                let drop_cur_id = self.adg.add_drop_node(drop, span);
                let rule_id = self.adg.add_rule_node("DF", 1.0);
                let alarm_id = self.adg.add_alarm_node(AlarmKind::DF, span);
                self.adg.add_edge(drop_before_id, rule_id);
                self.adg.add_edge(drop_cur_id, rule_id);
                self.adg.add_edge(rule_id, alarm_id);
            }
        }
        return self.values[drop].is_alive() == false;
    }

    pub fn dp_check(&mut self, current_block: &BlockNode<'tcx>) {
        match current_block.is_cleanup {
            true => {
                for i in 0..self.arg_size {
                    if self.values[i + 1].is_ptr() && self.is_dangling(i + 1).0 {
                        self.bug_records.dp_bugs_unwind.insert(self.span);
                    }
                }
            }
            false => {
                if self.values[0].may_drop {
                    let res = self.is_dangling(0);
                    if res.0 {
                        self.bug_records.dp_bugs.insert(self.span);

                        let drop_id = self.adg.get_drop_node(res.1).unwrap();
                        let rule_id = self.adg.add_rule_node("DP", 1.0);
                        let alarm_id = self.adg.add_alarm_node(AlarmKind::DP, self.span);

                        if res.1 == 0 {
                            self.adg.add_edge(drop_id, rule_id);
                            self.adg.add_edge(rule_id, alarm_id);
                        } else {
                            let alias_id = self.adg.add_alias_node(0, res.1);
                            let drop_rule_id = self
                                .adg
                                .add_rule_node(&format!("DropAlias {:?} -> {:?}", res.1, 0), 1.0);
                            let to_drop_id = self.adg.add_drop_node(0, self.span);
                            self.adg.add_edge(drop_id, drop_rule_id);
                            self.adg.add_edge(alias_id, drop_rule_id);
                            self.adg.add_edge(drop_rule_id, to_drop_id);

                            self.adg.add_edge(to_drop_id, rule_id);
                            self.adg.add_edge(rule_id, alarm_id);
                        }
                    }
                } else {
                    for i in 0..self.arg_size {
                        if self.values[i + 1].is_ptr() {
                            let res = self.is_dangling(i + 1);
                            if res.0 {
                                self.bug_records.dp_bugs.insert(self.span);

                                let drop_id = self.adg.add_drop_node(i + 1, self.span);
                                let rule_id = self.adg.add_rule_node("DP", 1.0);
                                let alarm_id = self.adg.add_alarm_node(AlarmKind::DP, self.span);

                                if res.1 == i + 1 {
                                    self.adg.add_edge(drop_id, rule_id);
                                    self.adg.add_edge(rule_id, alarm_id);
                                } else {
                                    let alias_id = self.adg.add_alias_node(i + 1, res.1);
                                    let drop_rule_id = self.adg.add_rule_node(
                                        &format!("DropAlias {:?} -> {:?}", res.1, 0),
                                        1.0,
                                    );
                                    let to_drop_id = self.adg.add_drop_node(i + 1, self.span);
                                    self.adg.add_edge(drop_id, drop_rule_id);
                                    self.adg.add_edge(alias_id, drop_rule_id);
                                    self.adg.add_edge(drop_rule_id, to_drop_id);

                                    self.adg.add_edge(to_drop_id, rule_id);
                                    self.adg.add_edge(rule_id, alarm_id);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    pub fn dead_node(
        &mut self,
        drop: usize,
        birth: usize,
        info: &SourceInfo,
        alias: bool,
        alias_dead_nodes: &mut HashSet<usize>,
        field_dead_nodes: &mut HashMap<usize, Vec<(usize, usize)>>,
    ) {
        //Rc drop
        if self.values[drop].is_corner_case() {
            return;
        }
        //check if there is a double free bug.
        if !alias && self.df_check(drop, info.span) {
            return;
        }
        if self.dead_record[drop] {
            return;
        } else {
            self.dead_record[drop] = true;
        }
        //drop their alias
        if self.alias_set[drop] != drop {
            // for i in self.values[drop].alias.clone().into_iter() {
            //     if self.values[i].is_ref() {
            //         continue;
            //     }
            //     self.dead_node(i, birth, info, true);
            // }
            for i in 0..self.values.len() {
                if !self.union_is_same(drop, i) || i == drop || self.values[i].is_ref() {
                    continue;
                }

                alias_dead_nodes.insert(i);
                self.dead_node(i, birth, info, true, alias_dead_nodes, field_dead_nodes);
            }
        }
        //drop the fields of the root node.
        //alias flag is used to avoid the fields of the alias are dropped repeatly.
        if alias == false {
            for i in self.values[drop].fields.clone().into_iter() {
                if self.values[drop].is_tuple() == true && self.values[i.1].need_drop == false {
                    continue;
                }
                field_dead_nodes
                    .entry(drop)
                    .or_insert(vec![])
                    .push(i.clone());
                self.dead_node(i.1, birth, info, false, alias_dead_nodes, field_dead_nodes);
            }
        }
        //SCC.
        if self.values[drop].birth < birth as isize && self.values[drop].may_drop {
            self.values[drop].dead();
        }
    }

    pub fn get_field_seq(&self, value: &ValueNode) -> Vec<usize> {
        let mut field_id_seq = vec![];
        let mut node_ref = value;
        while node_ref.field_id != usize::MAX {
            field_id_seq.push(node_ref.field_id);
            node_ref = &self.values[value.father];
        }
        return field_id_seq;
    }
}
