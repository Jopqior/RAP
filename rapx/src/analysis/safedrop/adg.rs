use rustc_span::Span;

use std::mem;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
};

use crate::rap_info;

#[derive(Debug, Clone)]
pub enum AlarmKind {
    UAF,
    DP,
    DF,
}

#[derive(Debug, Clone)]
pub enum RelationKind {
    Alias {
        left: usize,
        right: usize,
    },
    Drop {
        var: usize,
        span: Span,
    },
    Use {
        var: usize,
        span: Span,
    },

    Assign {
        left: usize,
        right: usize,
        span: Span,
    },
    Call {
        left: usize,
        right: usize,
        span: Span,
    },
}

pub enum RuleKind {
    AssignAlias,
    CallReturnAlias,
    AliasTransitivity,
    UAF,
    DP,
    DF,
}

#[derive(Debug, Clone)]
pub enum NodeKind {
    Relation {
        kind: RelationKind,
    },
    Rule {
        name: String,
        /// firing prob of the rule
        conditional_prob: f64,
    },
    Alarm {
        kind: AlarmKind,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub struct Node {
    pub id: usize,
    pub confidence: f64,
    pub prec_nodes: Vec<usize>,
    pub succ_nodes: Vec<usize>,
    pub kind: NodeKind,
}

pub struct AlarmDerivationGraph {
    pub nodes: HashMap<usize, Node>,
    pub next_id: usize,

    /// Maps (from, to) to the id of the node that represents the alias
    pub alias_map: HashMap<(usize, usize), usize>,
    /// Maps from the drop node to the id of the node that represents the drop
    pub drop_map: HashMap<usize, (HashMap<Span, usize>, usize)>,
    /// Set of alarm nodes
    pub alarm_set: HashSet<usize>,
}

impl AlarmDerivationGraph {
    pub fn new() -> Self {
        AlarmDerivationGraph {
            nodes: HashMap::new(),
            next_id: 0,
            alias_map: HashMap::new(),
            drop_map: HashMap::new(),
            alarm_set: HashSet::new(),
        }
    }

    #[inline(always)]
    fn next_id(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    pub fn add_use_node(&mut self, var: usize, span: Span) -> usize {
        let id = self.next_id();
        let node = Node {
            id,
            confidence: 1.0,
            prec_nodes: vec![],
            succ_nodes: vec![],
            kind: NodeKind::Relation {
                kind: RelationKind::Use { var, span },
            },
        };
        self.nodes.insert(id, node);
        id
    }

    pub fn add_alias_node(&mut self, left: usize, right: usize) -> usize {
        if left > right {
            return self.add_alias_node(right, left);
        }
        if !self.alias_map.contains_key(&(left, right)) {
            let id = self.next_id();
            let node = Node {
                id,
                confidence: 1.0,
                prec_nodes: vec![],
                succ_nodes: vec![],
                kind: NodeKind::Relation {
                    kind: RelationKind::Alias { left, right },
                },
            };
            self.nodes.insert(id, node);
            self.alias_map.insert((left, right), id);

            id
        } else {
            *self.alias_map.get(&(left, right)).unwrap()
        }
    }

    pub fn add_drop_node(&mut self, to_drop: usize, span: Span) -> usize {
        let id = self.next_id();
        if !self.drop_map.contains_key(&to_drop) {
            let node = Node {
                id,
                confidence: 1.0,
                prec_nodes: vec![],
                succ_nodes: vec![],
                kind: NodeKind::Relation {
                    kind: RelationKind::Drop { var: to_drop, span },
                },
            };
            self.nodes.insert(id, node);
            self.drop_map.insert(to_drop, (HashMap::new(), id));
            self.drop_map.get_mut(&to_drop).unwrap().0.insert(span, id);
        } else if let Some(vec) = self.drop_map.get_mut(&to_drop) {
            if let Some(existing_id) = vec.0.get(&span) {
                return *existing_id;
            }
            vec.0.insert(span, id);
            let node = Node {
                id,
                confidence: 1.0,
                prec_nodes: vec![],
                succ_nodes: vec![],
                kind: NodeKind::Relation {
                    kind: RelationKind::Drop { var: to_drop, span },
                },
            };
            self.nodes.insert(id, node);
            vec.1 = id;
        }

        id
    }

    pub fn get_drop_node(&self, to_drop: usize) -> Option<usize> {
        self.drop_map.get(&to_drop).and_then(|(_, id)| Some(*id))
    }

    pub fn add_assign_node(&mut self, left: usize, right: usize, span: Span) -> usize {
        let id = self.next_id();
        let node = Node {
            id,
            confidence: 1.0,
            prec_nodes: vec![],
            succ_nodes: vec![],
            kind: NodeKind::Relation {
                kind: RelationKind::Assign { left, right, span },
            },
        };
        self.nodes.insert(id, node);
        id
    }

    pub fn add_call_node(&mut self, left: usize, right: usize, span: Span) -> usize {
        let id = self.next_id();
        let node = Node {
            id,
            confidence: 1.0,
            prec_nodes: vec![],
            succ_nodes: vec![],
            kind: NodeKind::Relation {
                kind: RelationKind::Call { left, right, span },
            },
        };
        self.nodes.insert(id, node);
        id
    }

    pub fn add_rule_node(&mut self, name: &str, conditional_prob: f64) -> usize {
        let id = self.next_id();
        let node = Node {
            id,
            confidence: 1.0,
            prec_nodes: vec![],
            succ_nodes: vec![],
            kind: NodeKind::Rule {
                name: name.to_string(),
                conditional_prob,
            },
        };
        self.nodes.insert(id, node);
        id
    }

    pub fn add_alarm_node(&mut self, alarm_kind: AlarmKind, span: Span) -> usize {
        let id = self.next_id();
        let node = Node {
            id,
            confidence: 1.0,
            prec_nodes: vec![],
            succ_nodes: vec![],
            kind: NodeKind::Alarm {
                kind: alarm_kind,
                span,
            },
        };
        self.nodes.insert(id, node);
        self.alarm_set.insert(id);
        id
    }

    pub fn add_edge(&mut self, from: usize, to: usize) {
        if let Some(node) = self.nodes.get_mut(&from) {
            node.succ_nodes.push(to);
        }
        if let Some(node) = self.nodes.get_mut(&to) {
            node.prec_nodes.push(from);
        }
    }

    #[inline(always)]
    pub fn get_node(&self, id: usize) -> Option<&Node> {
        self.nodes.get(&id)
    }

    #[inline(always)]
    pub fn get_node_mut(&mut self, id: usize) -> Option<&mut Node> {
        self.nodes.get_mut(&id)
    }

    pub fn get_confidences(&self) -> HashMap<usize, f64> {
        self.nodes
            .iter()
            .map(|(id, node)| (*id, node.confidence))
            .collect()
    }

    pub fn remove_node(&mut self, id: usize) {
        if let Some(node) = self.nodes.remove(&id) {
            for &succ_id in &node.succ_nodes {
                if let Some(succ_node) = self.nodes.get_mut(&succ_id) {
                    succ_node.prec_nodes.retain(|&x| x != id);
                }
            }
            for &prec_id in &node.prec_nodes {
                if let Some(prec_node) = self.nodes.get_mut(&prec_id) {
                    prec_node.succ_nodes.retain(|&x| x != id);
                }
            }
        }
    }

    pub fn remove_edge(&mut self, from: usize, to: usize) {
        if let Some(node) = self.nodes.get_mut(&from) {
            node.succ_nodes.retain(|&x| x != to);
        }
        if let Some(node) = self.nodes.get_mut(&to) {
            node.prec_nodes.retain(|&x| x != from);
        }
    }

    pub fn remove_unreachable_nodes_from_alarm(&mut self) {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        for &alarm_id in &self.alarm_set {
            queue.push_back(alarm_id);
            visited.insert(alarm_id);
        }

        while let Some(node_id) = queue.pop_front() {
            if let Some(node) = self.nodes.get(&node_id) {
                for &prec_id in &node.prec_nodes {
                    if !visited.contains(&prec_id) {
                        visited.insert(prec_id);
                        queue.push_back(prec_id);
                    }
                }
            }
        }

        // Remove unreachable nodes
        let mut unreachable_nodes = self.nodes.keys().cloned().collect::<Vec<_>>();
        unreachable_nodes.retain(|id| !visited.contains(id));

        for id in unreachable_nodes {
            self.remove_node(id);
        }
    }

    pub fn calculate_alarm_confidences(&mut self) {
        // Simplified version of loopy belief propagation: DAG

        // 1. Initialization & Topological Sort
        let mut in_degs = HashMap::new();
        let mut queue = VecDeque::new();
        let mut computed_confidences = HashMap::new();

        for node in self.nodes.values() {
            let in_deg = node.prec_nodes.len();
            in_degs.insert(node.id, in_deg);

            match node.kind {
                NodeKind::Relation { .. } => {
                    if in_deg == 0 {
                        computed_confidences.insert(node.id, node.confidence);
                        queue.push_back(node.id);
                    } else {
                        computed_confidences.insert(node.id, -1.0);
                    }
                }
                NodeKind::Rule { .. } => {
                    computed_confidences.insert(node.id, -1.0);
                }
                NodeKind::Alarm { .. } => {
                    computed_confidences.insert(node.id, -1.0);
                }
            }
        }

        // 2. Forward propagation
        while let Some(node_id) = queue.pop_front() {
            let succ_nodes_clone = self
                .get_node(node_id)
                .map_or(Vec::new(), |node| node.succ_nodes.clone());

            for succ_id in succ_nodes_clone {
                if let Some(succ_node) = self.get_node_mut(succ_id) {
                    // Update succ_id's confidence based on all its computed predecessors
                    let mut all_preds_computed = true;
                    let mut preds_confidences = vec![];
                    for &pred_id in &succ_node.prec_nodes {
                        if let Some(pred_conf) = computed_confidences.get(&pred_id) {
                            if *pred_conf < 0.0 {
                                all_preds_computed = false;
                                break;
                            }
                            preds_confidences.push(*pred_conf);
                        }
                    }
                    if all_preds_computed && computed_confidences.get(&succ_id) == Some(&-1.0) {
                        let new_succ_conf = match succ_node.kind {
                            NodeKind::Rule {
                                name: _,
                                ref conditional_prob,
                            } => {
                                let rule_firing_prob = *conditional_prob;
                                let p_preds_met = preds_confidences.iter().product::<f64>();
                                rule_firing_prob * p_preds_met
                            }
                            NodeKind::Relation { .. } | NodeKind::Alarm { .. } => {
                                let prob_not_occurring =
                                    preds_confidences.iter().map(|&x| 1.0 - x).product::<f64>();
                                1.0 - prob_not_occurring
                            }
                        };
                        computed_confidences.insert(succ_id, new_succ_conf);
                    }
                }

                // Decrease in-degree of successors
                if let Some(in_deg) = in_degs.get_mut(&succ_id) {
                    *in_deg -= 1;
                    if *in_deg == 0 {
                        queue.push_back(succ_id);
                    }
                }
            }
        }

        // 3. Truly update the confidence of the nodes
        for node in self.nodes.values_mut() {
            if let Some(conf) = computed_confidences.get(&node.id) {
                node.confidence = *conf;
            }
        }
    }

    pub fn get_ranked_alarm_nodes(&self, confidences: &HashMap<usize, f64>) -> Vec<(usize, f64)> {
        let mut alarm_nodes: Vec<usize> = self.alarm_set.iter().cloned().collect();
        alarm_nodes.sort_by(|a, b| confidences[b].partial_cmp(&confidences[a]).unwrap());
        alarm_nodes
            .iter()
            .map(|&id| (id, confidences[&id]))
            .collect()
    }

    pub fn has_alarm(&self) -> bool {
        !self.alarm_set.is_empty()
    }

    pub fn compress_path(&mut self) {
        let mut srcs = HashMap::new();
        let mut sinks = HashMap::new();
        let mut e = HashSet::new();
        for node in self.nodes.values() {
            if let NodeKind::Rule { .. } = node.kind {
                continue;
            }
            srcs.insert(node.id, node.prec_nodes.clone());
            sinks.insert(node.id, node.succ_nodes.clone());
            if node.prec_nodes.len() == 1 && node.succ_nodes.len() == 1 {
                e.insert(node.id);
            }
        }
    }

    pub fn calculate_posterior_confidences(
        &mut self,
        evidence: &HashMap<usize, bool>,
    ) -> HashMap<usize, f64> {
        self.run_lbp(evidence, None, None)
    }

    pub fn run_lbp(
        &mut self,
        evidence: &HashMap<usize, bool>,
        max_iterations: Option<usize>,
        epsilon: Option<f64>,
    ) -> HashMap<usize, f64> {
        #[inline(always)]
        fn get_factor(node: &Node, i: usize) -> f64 {
            match node.kind {
                NodeKind::Rule {
                    name: _,
                    ref conditional_prob,
                } => {
                    if i == (1 << node.prec_nodes.len()) - 1 {
                        *conditional_prob
                    } else {
                        0.0
                    }
                }
                NodeKind::Relation { .. } | NodeKind::Alarm { .. } => {
                    if i == 0 {
                        0.0
                    } else {
                        1.0
                    }
                }
            }
        }

        #[inline(always)]
        fn normalize(msg: (f64, f64)) -> (f64, f64) {
            let sum = msg.0 + msg.1;
            if sum == 0.0 {
                (0.5, 0.5)
            } else {
                (msg.0 / sum, msg.1 / sum)
            }
        }

        let max_iterations = max_iterations.unwrap_or(1000);
        let epsilon = epsilon.unwrap_or(1e-4);

        // --- LBP Data ---
        // messages
        let mut pi_msgs: HashMap<(usize, usize), (f64, f64)> = HashMap::new();
        let mut new_pi_msgs: HashMap<(usize, usize), (f64, f64)> = HashMap::new();
        let mut lambda_msgs: HashMap<(usize, usize), (f64, f64)> = HashMap::new();
        let mut new_lambda_msgs: HashMap<(usize, usize), (f64, f64)> = HashMap::new();

        let mut lambda_self: HashMap<usize, (f64, f64)> = HashMap::new();

        // beliefs
        let mut beliefs: HashMap<usize, f64> = HashMap::new();
        let mut new_beliefs: HashMap<usize, f64> = HashMap::new();

        // --- Initialization ---
        for node in self.nodes.values() {
            if let Some(&is_true) = evidence.get(&node.id) {
                let p = if is_true { 1.0 } else { 0.0 };
                let q = 1.0 - p;
                lambda_self.insert(node.id, (p, q));
                beliefs.insert(node.id, p);
            } else {
                lambda_self.insert(node.id, (1.0, 1.0));
                beliefs.insert(node.id, node.confidence);
            }

            for &succ_id in node.succ_nodes.iter() {
                pi_msgs.insert((node.id, succ_id), (1.0, 1.0));
            }

            for &prec_id in node.prec_nodes.iter() {
                lambda_msgs.insert((node.id, prec_id), (1.0, 1.0));
            }
        }

        // --- LBP Iteration ---
        let mut iterations = 0;
        loop {
            if iterations >= max_iterations {
                eprintln!(
                    "Warning: LBP reached max iterations ({}) without converging.",
                    max_iterations
                );
                break;
            }
            // rap_info!("LBP Iteration: {}", iterations);

            let mut max_delta = 0.0;
            for node in self.nodes.values() {
                // 1. Calculate New In Messages
                let cur_lamdba_in = if let Some(&is_true) = evidence.get(&node.id) {
                    let p = if is_true { 1.0 } else { 0.0 };
                    (p, 1.0 - p)
                } else {
                    node.succ_nodes
                        .iter()
                        .map(|&child_id| lambda_msgs[&(child_id, node.id)])
                        .fold(lambda_self[&node.id], |acc, msg| {
                            (acc.0 * msg.0, acc.1 * msg.1)
                        })
                };

                let cur_pi_in = if node.prec_nodes.is_empty() {
                    (node.confidence, 1.0 - node.confidence)
                } else {
                    let mut res = (0.0, 0.0);
                    for i in 0..(1 << node.prec_nodes.len()) {
                        let mut prod = {
                            let factor = get_factor(node, i);
                            (factor, 1.0 - factor)
                        };

                        for (k, &prec_id) in node.prec_nodes.iter().enumerate() {
                            let msg = pi_msgs[&(prec_id, node.id)];
                            let cur = if (i >> k) & 1 == 1 { msg.0 } else { msg.1 };
                            prod.0 *= cur;
                            prod.1 *= cur;
                        }

                        res.0 += prod.0;
                        res.1 += prod.1;
                    }
                    res
                };

                // rap_info!(
                //     "Node {}: cur_lamdba_in: {:?}, cur_pi_in: {:?}",
                //     node.id,
                //     cur_lamdba_in,
                //     cur_pi_in
                // );

                // 2. Calculate New Beliefs
                if evidence.contains_key(&node.id) {
                    new_beliefs.insert(node.id, beliefs[&node.id]);
                } else {
                    let new_belief =
                        normalize((cur_lamdba_in.0 * cur_pi_in.0, cur_lamdba_in.1 * cur_pi_in.1)).0;
                    new_beliefs.insert(node.id, new_belief);

                    let delta = (new_belief - beliefs[&node.id]).abs();
                    if delta > max_delta {
                        max_delta = delta;
                    }
                }

                // 3. Calculate New Out Messages
                for (i, &prec_id) in node.prec_nodes.iter().enumerate() {
                    let new_lambda_out = {
                        let mut res = (0.0, 0.0);
                        let mut sum_of_x_true = (0.0, 0.0);
                        let mut sum_of_x_false = (0.0, 0.0);

                        for j in 0..((1 << node.prec_nodes.len()) >> 1) {
                            let mask_of_ui_false = ((j >> i) << (i + 1)) | (j & ((1 << i) - 1));
                            let mask_of_ui_true = mask_of_ui_false | (1 << i);
                            let factor_of_ui_false = get_factor(node, mask_of_ui_false);
                            let factor_of_ui_true = get_factor(node, mask_of_ui_true);

                            let mut prod_of_uk = 1.0;
                            for (k, &k_id) in node.prec_nodes.iter().enumerate() {
                                if k != i {
                                    let msg = pi_msgs[&(k_id, node.id)];
                                    let cur = if (mask_of_ui_false >> k) & 1 == 1 {
                                        msg.0
                                    } else {
                                        msg.1
                                    };
                                    prod_of_uk *= cur;
                                }
                            }

                            sum_of_x_true.0 += factor_of_ui_true * prod_of_uk;
                            sum_of_x_true.1 += factor_of_ui_false * prod_of_uk;

                            sum_of_x_false.0 += (1.0 - factor_of_ui_true) * prod_of_uk;
                            sum_of_x_false.1 += (1.0 - factor_of_ui_false) * prod_of_uk;
                        }

                        res.0 =
                            cur_lamdba_in.0 * sum_of_x_true.0 + cur_lamdba_in.1 * sum_of_x_false.0;
                        res.1 =
                            cur_lamdba_in.0 * sum_of_x_true.1 + cur_lamdba_in.1 * sum_of_x_false.1;
                        normalize(res)
                    };

                    new_lambda_msgs.insert((node.id, prec_id), new_lambda_out);
                }

                for &succ_id in &node.succ_nodes {
                    let tot_prod_of_lambda_msgs_except_self = node
                        .succ_nodes
                        .iter()
                        .filter(|&&id| id != succ_id)
                        .map(|&succ_id| lambda_msgs[&(succ_id, node.id)])
                        .fold((1.0, 1.0), |acc, msg| (acc.0 * msg.0, acc.1 * msg.1));
                    let new_pi_out = {
                        let res = (
                            cur_pi_in.0
                                * lambda_self[&succ_id].0
                                * tot_prod_of_lambda_msgs_except_self.0,
                            cur_pi_in.1
                                * lambda_self[&succ_id].1
                                * tot_prod_of_lambda_msgs_except_self.1,
                        );

                        normalize(res)
                    };

                    new_pi_msgs.insert((node.id, succ_id), new_pi_out);
                }
            }

            if max_delta < epsilon {
                println!(
                    "LBP converged after {} iterations (max_delta: {}).",
                    iterations, max_delta
                );
                break;
            }

            // 4. Update Beliefs and Messages
            mem::swap(&mut beliefs, &mut new_beliefs);
            mem::swap(&mut pi_msgs, &mut new_pi_msgs);
            mem::swap(&mut lambda_msgs, &mut new_lambda_msgs);

            iterations += 1;
        }

        beliefs
    }
}

impl fmt::Debug for AlarmDerivationGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Alarm Derivation Graph:")?;
        for node in self.nodes.values() {
            writeln!(f, "Node {}: {:?}", node.id, node)?;
        }
        Ok(())
    }
}
