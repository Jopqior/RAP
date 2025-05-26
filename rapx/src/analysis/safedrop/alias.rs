use std::collections::HashSet;

use rustc_middle::mir::{Operand, Place, ProjectionElem, TerminatorKind};
use rustc_middle::ty;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::adg::AlarmKind;
use super::graph::*;
use super::types::*;
use crate::analysis::core::alias::{FnMap, RetAlias};
use crate::{rap_error, rap_info};

impl<'tcx> SafeDropGraph<'tcx> {
    /* alias analysis for a single block */
    pub fn alias_bb(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>) {
        rap_info!("(alias_bb) Found block {:?}", bb_index);
        for stmt in self.blocks[bb_index].const_value.clone() {
            self.constant.insert(stmt.0, stmt.1);
        }
        let cur_block = self.blocks[bb_index].clone();
        for assign in cur_block.assignments {
            let mut lv_aliaset_idx = self.projection(tcx, false, assign.lv);
            let rv_aliaset_idx = self.projection(tcx, true, assign.rv);
            match assign.atype {
                AssignType::Variant => {
                    self.alias_set[lv_aliaset_idx] = rv_aliaset_idx;
                    continue;
                }
                AssignType::InitBox => {
                    lv_aliaset_idx = *self.values[lv_aliaset_idx].fields.get(&0).unwrap();
                }
                _ => {} // Copy or Move
            }

            rap_info!(
                "(alias_bb) Found assign: {:?} = {:?}, lv_aliaset_idx: {:?}, rv_aliaset_idx: {:?}",
                assign.lv,
                assign.rv,
                lv_aliaset_idx,
                rv_aliaset_idx
            );
            let exist_bug = self.uaf_check(
                rv_aliaset_idx,
                assign.span,
                assign.rv.local.as_usize(),
                false,
            );

            // add adg node
            if exist_bug.0 {
                rap_info!("(alias_bb) Found UAF {:?}", assign.span);

                // add drop node
                let drop_id = self.adg.get_drop_node(exist_bug.1).unwrap();
                rap_info!(
                    "(alias_bb) Drop {:?} at {:?}",
                    exist_bug.1,
                    self.adg.get_node(drop_id).unwrap().kind
                );

                // add use node
                rap_info!("(alias_bb) Use {:?}", rv_aliaset_idx);
                let use_id = self.adg.add_use_node(rv_aliaset_idx, assign.span);

                // add rule node
                let rule_id = self.adg.add_rule_node("UAF", 0.999);

                // add alarm node for use-after-free
                let alarm_id = self.adg.add_alarm_node(AlarmKind::UAF, assign.span);

                if exist_bug.1 == rv_aliaset_idx {
                    self.adg.add_edge(drop_id, rule_id);
                    self.adg.add_edge(use_id, rule_id);
                    self.adg.add_edge(rule_id, alarm_id);
                } else {
                    let alias_id = self.adg.add_alias_node(rv_aliaset_idx, exist_bug.1);
                    let drop_rule_id = self.adg.add_rule_node(
                        &format!("DropAlias {:?} -> {:?}", exist_bug.1, rv_aliaset_idx),
                        1.0,
                    );
                    let to_drop_id = self.adg.add_drop_node(rv_aliaset_idx, assign.span);
                    self.adg.add_edge(drop_id, drop_rule_id);
                    self.adg.add_edge(alias_id, drop_rule_id);
                    self.adg.add_edge(drop_rule_id, to_drop_id);

                    self.adg.add_edge(to_drop_id, rule_id);
                    self.adg.add_edge(use_id, rule_id);
                    self.adg.add_edge(rule_id, alarm_id);
                }
            }

            self.fill_birth(lv_aliaset_idx, self.scc_indices[bb_index] as isize);
            if self.values[lv_aliaset_idx].local != self.values[rv_aliaset_idx].local {
                self.handle_merge_alias(lv_aliaset_idx, rv_aliaset_idx, true, assign.span);
            }
        }
    }

    /* Check the aliases introduced by the terminators (function call) of a scc block */
    pub fn alias_bbcall(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, fn_map: &FnMap) {
        let cur_block = self.blocks[bb_index].clone();
        for call in cur_block.calls {
            if let TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                target: _,
                unwind: _,
                call_source: _,
                fn_span: _,
            } = call.kind
            {
                rap_info!(
                    "(alias_bbcall) Found call: {:?} = {:?} {:?}",
                    destination,
                    func,
                    args
                );

                if let Operand::Constant(ref constant) = func {
                    let lv = self.projection(tcx, false, destination.clone());
                    self.values[lv].birth = self.scc_indices[bb_index] as isize;
                    let mut merge_vec = Vec::new();
                    merge_vec.push(lv);
                    let mut may_drop_flag = 0;
                    if self.values[lv].may_drop {
                        may_drop_flag += 1;
                    }
                    for arg in args {
                        match arg.node {
                            Operand::Copy(ref p) => {
                                let rv = self.projection(tcx, true, p.clone());
                                let exist_bug = self.uaf_check(
                                    rv,
                                    call.source_info.span,
                                    p.local.as_usize(),
                                    true,
                                );

                                if exist_bug.0 {
                                    rap_info!("(alias_bbcall) Found UAF for copy arg");

                                    // add alarm node for use-after-free
                                    let alarm_id = self
                                        .adg
                                        .add_alarm_node(AlarmKind::UAF, call.source_info.span);

                                    // add drop node
                                    let drop_id = self.adg.get_drop_node(exist_bug.1).unwrap();
                                    rap_info!(
                                        "(alias_bbcall) Drop {:?} at {:?}",
                                        exist_bug.1,
                                        self.adg.get_node(drop_id).unwrap().kind
                                    );

                                    // add use node
                                    rap_info!("(alias_bbcall) Use {:?}", rv);
                                    let use_id = self.adg.add_use_node(rv, call.source_info.span);

                                    // add rule node
                                    let rule_id = self.adg.add_rule_node("UAF", 0.9);

                                    if exist_bug.1 == rv {
                                        self.adg.add_edge(drop_id, rule_id);
                                        self.adg.add_edge(use_id, rule_id);
                                        self.adg.add_edge(rule_id, alarm_id);
                                    } else {
                                        let alias_id = self.adg.add_alias_node(rv, exist_bug.1);
                                        let drop_rule_id = self.adg.add_rule_node(
                                            &format!("DropAlias {:?} -> {:?}", exist_bug.1, rv),
                                            1.0,
                                        );
                                        let to_drop_id =
                                            self.adg.add_drop_node(rv, call.source_info.span);
                                        self.adg.add_edge(drop_id, drop_rule_id);
                                        self.adg.add_edge(alias_id, drop_rule_id);
                                        self.adg.add_edge(drop_rule_id, to_drop_id);

                                        self.adg.add_edge(to_drop_id, rule_id);
                                        self.adg.add_edge(use_id, rule_id);
                                        self.adg.add_edge(rule_id, alarm_id);
                                    }
                                }

                                merge_vec.push(rv);
                                if self.values[rv].may_drop {
                                    may_drop_flag += 1;
                                }
                            }
                            Operand::Move(ref p) => {
                                let rv = self.projection(tcx, true, p.clone());
                                let exist_bug = self.uaf_check(
                                    rv,
                                    call.source_info.span,
                                    p.local.as_usize(),
                                    true,
                                );

                                if exist_bug.0 {
                                    rap_info!("(alias_bbcall) Found UAF for move arg");

                                    // add drop node
                                    let drop_id = self.adg.get_drop_node(exist_bug.1).unwrap();
                                    rap_info!(
                                        "(alias_bbcall) Drop {:?} at {:?}",
                                        exist_bug.1,
                                        self.adg.get_node(drop_id).unwrap().kind
                                    );

                                    // add use node
                                    rap_info!("(alias_bbcall) Use {:?}", rv);
                                    let use_id = self.adg.add_use_node(rv, call.source_info.span);

                                    // add rule node
                                    let rule_id = self.adg.add_rule_node("UAF", 0.9);

                                    // add alarm node for use-after-free
                                    let alarm_id = self
                                        .adg
                                        .add_alarm_node(AlarmKind::UAF, call.source_info.span);

                                    if exist_bug.1 == rv {
                                        self.adg.add_edge(drop_id, rule_id);
                                        self.adg.add_edge(use_id, rule_id);
                                        self.adg.add_edge(rule_id, alarm_id);
                                    } else {
                                        let alias_id = self.adg.add_alias_node(rv, exist_bug.1);
                                        let drop_rule_id = self.adg.add_rule_node(
                                            &format!("DropAlias {:?} -> {:?}", exist_bug.1, rv),
                                            1.0,
                                        );
                                        let to_drop_id =
                                            self.adg.add_drop_node(rv, call.source_info.span);
                                        self.adg.add_edge(drop_id, drop_rule_id);
                                        self.adg.add_edge(alias_id, drop_rule_id);
                                        self.adg.add_edge(drop_rule_id, to_drop_id);

                                        self.adg.add_edge(to_drop_id, rule_id);
                                        self.adg.add_edge(use_id, rule_id);
                                        self.adg.add_edge(rule_id, alarm_id);
                                    }
                                }

                                merge_vec.push(rv);
                                if self.values[rv].may_drop {
                                    may_drop_flag += 1;
                                }
                            }
                            Operand::Constant(_) => {
                                merge_vec.push(0);
                            }
                        }
                    }
                    if let ty::FnDef(ref target_id, _) = constant.const_.ty().kind() {
                        if may_drop_flag > 1 {
                            if tcx.is_mir_available(*target_id) {
                                rap_info!(
                                    "(alias_bbcall) Found function call: {:?} with may_drop > 1",
                                    target_id
                                );
                                if fn_map.contains_key(&target_id) {
                                    let assignments = fn_map.get(&target_id).unwrap();
                                    for assign in assignments.aliases().iter() {
                                        if !assign.valuable() {
                                            continue;
                                        }
                                        self.merge(assign, &merge_vec, call.source_info.span);
                                    }
                                }
                            } else {
                                rap_info!(
                                    "(alias_bbcall) Found function call: {:?} but MIR not available, lv.may_drop: {:?}",
                                    target_id,
                                    self.values[lv].may_drop
                                );
                                if self.values[lv].may_drop {
                                    use crate::analysis::utils::intrinsic_id::CLONE;
                                    if target_id.index.as_usize() == CLONE {
                                        let mut rv_aliaset_idx = 0;
                                        for rv in &merge_vec {
                                            if lv != *rv {
                                                rv_aliaset_idx = *rv;
                                                break;
                                            }
                                        }
                                        self.handle_merge_alias(lv, rv_aliaset_idx, false, call.source_info.span);
                                    }
                                    if self.corner_handle(lv, &merge_vec, *target_id) {
                                        rap_info!("(alias_bbcall) corner case {:?}", target_id);
                                        continue;
                                    }
                                    let mut right_set = Vec::new();
                                    for rv in &merge_vec {
                                        if self.values[*rv].may_drop
                                            && lv != *rv
                                            && self.values[lv].is_ptr()
                                        {
                                            right_set.push(*rv);
                                        }
                                    }
                                    if right_set.len() == 1 {
                                        // self.merge_alias(lv, right_set[0]);
                                        self.handle_merge_alias(lv, right_set[0], false, call.source_info.span);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // assign to the variable _x, we will set the birth of _x and its child self.values a new birth.
    pub fn fill_birth(&mut self, node: usize, birth: isize) {
        self.values[node].birth = birth;
        for i in 0..self.values.len() {
            if self.union_is_same(i, node) && self.values[i].birth == -1 {
                self.values[i].birth = birth;
            }
        }
        for i in self.values[node].fields.clone().into_iter() {
            self.fill_birth(i.1, birth); //i.1 corresponds to the local field.
        }
    }

    /*
     * This is the function for field sensitivity
     * If the projection is a deref, we directly return its head alias or alias[0].
     * If the id is not a ref, we further make the id and its first element an alias, i.e., level-insensitive
     *
     */
    pub fn projection(&mut self, tcx: TyCtxt<'tcx>, is_right: bool, place: Place<'tcx>) -> usize {
        let mut local = place.local.as_usize();
        let mut proj_id = local;
        for proj in place.projection {
            let new_id = self.values.len();
            match proj {
                ProjectionElem::Deref => {
                    //proj_id = self.values[proj_id].alias[0];
                    proj_id = self.alias_set[proj_id];
                }
                /*
                 * Objective: 2 = 1.0; 0 = 2.0; => 0 = 1.0.0
                 */
                ProjectionElem::Field(field, ty) => {
                    if is_right && self.alias_set[proj_id] != proj_id {
                        proj_id = self.alias_set[proj_id];
                        local = self.values[proj_id].local;
                    }
                    let field_idx = field.as_usize();
                    if !self.values[proj_id].fields.contains_key(&field_idx) {
                        let param_env = tcx.param_env(self.def_id);
                        let need_drop = ty.needs_drop(tcx, param_env);
                        let may_drop = !is_not_drop(tcx, ty);
                        let mut node =
                            ValueNode::new(new_id, local, need_drop, need_drop || may_drop);
                        node.kind = kind(ty);
                        node.birth = self.values[proj_id].birth;
                        node.field_id = field_idx;
                        self.values[proj_id].fields.insert(field_idx, node.index);
                        self.alias_set.push(self.alias_set.len());
                        self.dead_record.push(false);
                        self.values.push(node);
                    }
                    proj_id = *self.values[proj_id].fields.get(&field_idx).unwrap();
                }
                _ => {}
            }
        }
        return proj_id;
    }

    fn handle_merge_alias(
        &mut self,
        lv_aliaset_idx: usize,
        rv_aliaset_idx: usize,
        assign_or_call: bool,
        span: Span,
    ) {
        let mut left_set = HashSet::new();
        let mut right_set = HashSet::new();
        let in_same_set = self.union_is_same(lv_aliaset_idx, rv_aliaset_idx);
        if !in_same_set {
            for i in 0..self.values.len() {
                if i != lv_aliaset_idx && self.union_is_same(i, lv_aliaset_idx) {
                    left_set.insert(i);
                }
                if i != rv_aliaset_idx && self.union_is_same(i, rv_aliaset_idx) {
                    right_set.insert(i);
                }
            }
        }

        self.merge_alias(lv_aliaset_idx, rv_aliaset_idx);

        if !in_same_set {
            let lr_assign_or_call_id = if assign_or_call {
                self.adg
                    .add_assign_node(lv_aliaset_idx, rv_aliaset_idx, span)
            } else {
                self.adg.add_call_node(lv_aliaset_idx, rv_aliaset_idx, span)
            };
            let lr_rule_id = if assign_or_call {
                self.adg.add_rule_node(
                    &format!("Assign {:?} = {:?}", lv_aliaset_idx, rv_aliaset_idx),
                    1.0,
                )
            } else {
                self.adg.add_rule_node(
                    &format!("Call {:?} = {:?}", lv_aliaset_idx, rv_aliaset_idx),
                    0.9,
                )
            };
            let lr_id = self.adg.add_alias_node(lv_aliaset_idx, rv_aliaset_idx);
            self.adg.add_edge(lr_assign_or_call_id, lr_rule_id);
            self.adg.add_edge(lr_rule_id, lr_id);

            for &i in &left_set {
                let il_id = self.adg.add_alias_node(i, lv_aliaset_idx);
                let ir_rule_id = self.adg.add_rule_node("Alias", 1.0);
                let ir_id = self.adg.add_alias_node(i, rv_aliaset_idx);
                self.adg.add_edge(il_id, ir_rule_id);
                self.adg.add_edge(lr_id, ir_rule_id);
                self.adg.add_edge(ir_rule_id, ir_id);
            }
            for &j in &right_set {
                let jr_id = self.adg.add_alias_node(j, rv_aliaset_idx);
                let jl_rule_id = self.adg.add_rule_node("Alias", 1.0);
                let jl_id = self.adg.add_alias_node(j, lv_aliaset_idx);
                self.adg.add_edge(jr_id, jl_rule_id);
                self.adg.add_edge(lr_id, jl_rule_id);
                self.adg.add_edge(jl_rule_id, jl_id);
            }
            for &i in &left_set {
                for &j in &right_set {
                    let ir_id = self.adg.add_alias_node(i, rv_aliaset_idx);
                    let jr_id = self.adg.add_alias_node(j, rv_aliaset_idx);
                    let ij_rule_id = self.adg.add_rule_node("Alias", 1.0);
                    let ij_id = self.adg.add_alias_node(i, j);
                    self.adg.add_edge(ir_id, ij_rule_id);
                    self.adg.add_edge(jr_id, ij_rule_id);
                    self.adg.add_edge(ij_rule_id, ij_id);
                }
            }
        }
    }

    //instruction to assign alias for a variable.
    pub fn merge_alias(&mut self, lv: usize, rv: usize) {
        // if self.values[lv].alias.len() > 1 {
        //     let mut alias_clone = self.values[rv].alias.clone();
        //     self.values[lv].alias.append(&mut alias_clone);
        // } else {
        //     self.values[lv].alias = self.values[rv].alias.clone();
        // }
        if lv > self.values.len() || rv > self.values.len() {
            return;
        }
        rap_info!("(merge_alias) Merge alias {:?} and {:?}", lv, rv);
        self.union_merge(lv, rv);
        for field in self.values[rv].fields.clone().into_iter() {
            if !self.values[lv].fields.contains_key(&field.0) {
                let mut node = ValueNode::new(
                    self.values.len(),
                    self.values[lv].local,
                    self.values[field.1].need_drop,
                    self.values[field.1].may_drop,
                );
                node.kind = self.values[field.1].kind;
                node.birth = self.values[lv].birth;
                node.field_id = field.0;
                self.values[lv].fields.insert(field.0, node.index);
                self.alias_set.push(self.alias_set.len());
                self.dead_record.push(false);
                self.values.push(node);
            }
            let lv_field = *(self.values[lv].fields.get(&field.0).unwrap());
            self.merge_alias(lv_field, field.1);
        }
    }

    //inter-procedure instruction to merge alias.
    pub fn merge(&mut self, ret_alias: &RetAlias, arg_vec: &Vec<usize>, func_span: Span) {
        if ret_alias.left_index >= arg_vec.len() || ret_alias.right_index >= arg_vec.len() {
            rap_error!("Vector error!");
            return;
        }
        let left_init = arg_vec[ret_alias.left_index];
        let mut right_init = arg_vec[ret_alias.right_index];
        let mut lv = left_init;
        let mut rv = right_init;
        for index in ret_alias.left_field_seq.iter() {
            if self.values[lv].fields.contains_key(&index) == false {
                let need_drop = ret_alias.left_need_drop;
                let may_drop = ret_alias.left_may_drop;
                let mut node = ValueNode::new(self.values.len(), left_init, need_drop, may_drop);
                node.kind = TyKind::RawPtr;
                node.birth = self.values[lv].birth;
                node.field_id = *index;
                self.values[lv].fields.insert(*index, node.index);
                self.alias_set.push(self.alias_set.len());
                self.dead_record.push(false);
                self.values.push(node);
            }
            lv = *self.values[lv].fields.get(&index).unwrap();
        }
        for index in ret_alias.right_field_seq.iter() {
            // if self.values[rv].alias[0] != rv {
            if self.union_is_same(rv, self.alias_set[rv]) {
                rv = self.values[rv].index;
                right_init = self.values[rv].local;
            }
            if !self.values[rv].fields.contains_key(&index) {
                let need_drop = ret_alias.right_need_drop;
                let may_drop = ret_alias.right_may_drop;
                let mut node =
                    ValueNode::new(self.alias_set.len(), right_init, need_drop, may_drop);
                node.kind = TyKind::RawPtr;
                node.birth = self.values[rv].birth;
                node.field_id = *index;
                self.values[rv].fields.insert(*index, node.index);
                self.alias_set.push(self.values.len());
                self.dead_record.push(false);
                self.values.push(node);
            }
            rv = *self.values[rv].fields.get(&index).unwrap();
        }
        self.handle_merge_alias(lv, rv, false, func_span);
    }

    #[inline(always)]
    pub fn union_find(&mut self, e: usize) -> usize {
        let mut r = e;
        while self.alias_set[r] != r {
            r = self.alias_set[r];
        }
        r
    }

    #[inline(always)]
    pub fn union_merge(&mut self, e1: usize, e2: usize) {
        let f1 = self.union_find(e1);
        let f2 = self.union_find(e2);

        if f1 < f2 {
            self.alias_set[f2] = f1;
        }
        if f1 > f2 {
            self.alias_set[f1] = f2;
        }

        for member in 0..self.alias_set.len() {
            self.alias_set[member] = self.union_find(self.alias_set[member]);
        }
    }

    #[inline(always)]
    pub fn union_is_same(&mut self, e1: usize, e2: usize) -> bool {
        let f1 = self.union_find(e1);
        let f2 = self.union_find(e2);
        f1 == f2
    }

    #[inline(always)]
    pub fn union_has_alias(&mut self, e: usize) -> bool {
        for i in 0..self.alias_set.len() {
            if i == e {
                continue;
            }
            if self.union_is_same(e, i) {
                return true;
            }
        }
        false
    }
}
