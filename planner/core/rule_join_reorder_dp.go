// Copyright 2018 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"math/bits"

	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	nodeIDs    []int
	nodeIDMask uint
	expr       expression.Expression
}

func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	// TODO: You need to implement the join reorder algo based on DP.

	// The pseudo code can be found in README.
	// And there's some common struct and method like `baseNodeCumCost`, `calcJoinCumCost` you can use in `rule_join_reorder.go`.
	// Also, you can take a look at `rule_join_reorder_greedy.go`, this file implement the join reorder algo based on greedy algorithm.
	// You'll see some common usages in the greedy version.

	// Note that the join tree may be disconnected. i.e. You need to consider the case `select * from t, t1, t2`.
	for _, jg := range joinGroup {
		jr := &jrNode{
			p:       jg,
			cumCost: s.baseNodeCumCost(jg),
		}

		s.curJoinGroup = append(s.curJoinGroup, jr)
	}

	edges := make([][]int, len(joinGroup))
	allEqEdges := make([]joinGroupEqEdge, 0, len(joinGroup))

	for _, cond := range eqConds {
		sf := cond.(*expression.ScalarFunction)

		lCol := sf.GetArgs()[0].(*expression.Column)
		rCol := sf.GetArgs()[1].(*expression.Column)

		lIdx, err := findNodeIndexInGroup(joinGroup, lCol)
		if err != nil {
			return nil, err
		}
		rIdx, err := findNodeIndexInGroup(joinGroup, rCol)
		if err != nil {
			return nil, err
		}

		edges[lIdx] = append(edges[lIdx], rIdx)
		edges[rIdx] = append(edges[rIdx], lIdx)

		allEqEdges = append(allEqEdges, joinGroupEqEdge{
			nodeIDs: []int{lIdx, rIdx},
			edge:    sf,
		})
	}

	var joins []LogicalPlan
	connectedRels := make([]bool, len(joinGroup))

	for i := 0; i < len(joinGroup); i++ {
		if connectedRels[i] {
			continue
		}

		subGroup2OriginGroup := s.findConnectedSubGraphs(i, connectedRels, edges)

		join, err := s.dpSub(subGroup2OriginGroup, allEqEdges)
		if err != nil {
			return nil, err
		}

		joins = append(joins, join)
	}

	return s.makeBushyJoin(joins, nil), nil
}

func (s *joinReorderDPSolver) findConnectedSubGraphs(relIdx int, connectedRels []bool, edges [][]int) (subGroup2OriginGroup map[int]int) {
	subGroup2OriginGroup = make(map[int]int)
	queue := []int{relIdx}
	connectedRels[relIdx] = true

	i := 0

	for len(queue) > 0 {
		curNodeID := queue[0]
		queue = queue[1:]
		subGroup2OriginGroup[i] = curNodeID
		i += 1

		for _, adjNodeID := range edges[curNodeID] {
			if connectedRels[adjNodeID] {
				continue
			}
			queue = append(queue, adjNodeID)
			connectedRels[adjNodeID] = true
		}
	}
	return
}

func (s *joinReorderDPSolver) dpSub(subGroup2OriginGroup map[int]int, allEqEdges []joinGroupEqEdge) (LogicalPlan, error) {
	relationCount := len(subGroup2OriginGroup)

	dp := make([]*jrNode, 1<<relationCount)
	for i, g := range subGroup2OriginGroup {
		dp[1<<i] = s.curJoinGroup[g]
	}

	for state := uint(1); state < 1<<relationCount; state++ {
		if bits.OnesCount(state) == 1 {
			continue
		}
		for sub := (state - 1) & state; sub > 0; sub = (sub - 1) & state {
			remain := state ^ sub
			if sub > remain {
				continue
			}
			if dp[sub] == nil || dp[remain] == nil {
				continue
			}
			usedEdges := s.isRelationsConnected(sub, remain, subGroup2OriginGroup, allEqEdges)
			if len(usedEdges) == 0 {
				continue
			}
			newJoin, err := s.newJoinWithEdge(dp[sub].p, dp[remain].p, usedEdges, nil)
			if err != nil {
				return nil, err
			}
			curCost := s.calcJoinCumCost(newJoin, dp[sub], dp[remain])
			if dp[state] == nil {
				dp[state] = &jrNode{
					p:       newJoin,
					cumCost: curCost,
				}
			} else if curCost < dp[state].cumCost {
				dp[state].p = newJoin
				dp[state].cumCost = curCost
			}
		}
	}

	return dp[(1<<relationCount)-1].p, nil
}

func (s *joinReorderDPSolver) isRelationsConnected(sub, remain uint, subToOrig map[int]int, joinEqEdges []joinGroupEqEdge) []joinGroupEqEdge {
	var (
		resEqEdges []joinGroupEqEdge
	)
	isInRelationGroup := func(group, idx uint) bool {
		return group&(1<<idx) != 0
	}
	for _, edge := range joinEqEdges {
		lIdx := uint(subToOrig[edge.nodeIDs[0]])
		rIdx := uint(subToOrig[edge.nodeIDs[1]])
		if (isInRelationGroup(sub, lIdx) && isInRelationGroup(remain, rIdx)) ||
			(isInRelationGroup(remain, lIdx) && isInRelationGroup(sub, rIdx)) {
			resEqEdges = append(resEqEdges, edge)
		}
	}

	return resEqEdges
}

func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}
