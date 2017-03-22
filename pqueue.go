// Package pqueue provides an implementation of priority queue derived from the
// work done by Robert Sedgewick and Kevin Wayne as part of Algorithms, 4th
// Edition.
//
// http://algs4.cs.princeton.edu/code/
//
// Copyright (C) 2000–2016 Robert Sedgewick and Kevin Wayne
// Copyright (C) 2017 Kasper Kronborg Isager
//
// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
// details.
//
// You should have received a copy of the GNU General Public License along with
// this program.  If not, see <http://www.gnu.org/licenses/>.
package pqueue

import (
	"errors"
)

// PriorityQueue describes a priority queue data structure used for ordering a
// set of keys according to their priority.
type PriorityQueue interface {
	// Size gets the current number of keys within the priority queue.
	Size() int

	// Push adds a key with a priority to the priority queue.
	Push(key int, priority float32)

	// Pop removes and returns the head of the priority queue.
	Pop() (int, error)

	// Peek returns the head of the priority queue.
	Peek() (int, error)

	// Priority returns the priority of a key in the priority queue.
	Priority(key int) (float32, error)

	// Update changes the priority of a key in the priority queue.
	Update(key int, priority float32) error

	// Remove removes a key from the priority queue.
	Remove(key int) error
}

// Order describes the ordering of a priority queue.
type Order int

const (
	// Ascending ordering; smallest key at the head.
	Ascending Order = iota
	// Descending ordering; largest key at the head.
	Descending
)

type node struct {
	key      int
	priority float32
}

type heap struct {
	order Order
	nodes map[int]*node
	index map[int]int
	size  int
}

// New constructs and initialises a new priority queue.
func New(order Order) PriorityQueue {
	return &heap{
		order: order,
		nodes: make(map[int]*node),
		index: make(map[int]int),
		size:  0,
	}
}

func (heap heap) Size() int {
	return heap.size
}

func (heap *heap) Push(key int, priority float32) {
	heap.size++

	heap.nodes[heap.size] = &node{key, priority}
	heap.index[key] = heap.size

	heap.swim(heap.size)
}

func (heap *heap) Pop() (int, error) {
	if heap.size == 0 {
		return 0, errors.New("Queue is empty")
	}

	head := heap.nodes[1]

	heap.swap(1, heap.size)

	delete(heap.nodes, heap.size)
	delete(heap.index, head.key)

	heap.size--

	heap.sink(1)

	return head.key, nil
}

func (heap heap) Peek() (int, error) {
	if heap.size == 0 {
		return 0, errors.New("Queue is empty")
	}

	return heap.nodes[1].key, nil
}

func (heap heap) Priority(key int) (float32, error) {
	index, ok := heap.index[key]

	if !ok {
		return 0, errors.New("No such key")
	}

	return heap.nodes[index].priority, nil
}

func (heap *heap) Update(key int, priority float32) error {
	index, ok := heap.index[key]

	if !ok {
		return errors.New("No such key")
	}

	heap.nodes[index].priority = priority

	heap.swim(index)
	heap.sink(index)

	return nil
}

func (heap *heap) Remove(key int) error {
	index, ok := heap.index[key]

	if !ok {
		return errors.New("No such key")
	}

	heap.swap(index, heap.size)

	delete(heap.nodes, heap.size)
	delete(heap.index, key)

	heap.size--

	heap.swim(index)
	heap.sink(index)

	return nil
}

func (heap heap) ordered(i int, j int) bool {
	if heap.order == Ascending {
		return heap.nodes[i].priority <= heap.nodes[j].priority
	}

	return heap.nodes[i].priority >= heap.nodes[j].priority
}

func (heap *heap) swap(i int, j int) {
	nodes := heap.nodes
	index := heap.index

	nodes[i], nodes[j] = nodes[j], nodes[i]

	index[nodes[i].key] = i
	index[nodes[j].key] = j
}

func (heap *heap) swim(k int) {
	for k > 1 && !heap.ordered(k/2, k) {
		heap.swap(k/2, k)
		k = k / 2
	}
}

func (heap *heap) sink(k int) {
	for 2*k <= heap.size {
		j := 2 * k

		if j < heap.size && !heap.ordered(j, j+1) {
			j++
		}

		if heap.ordered(k, j) {
			break
		}

		heap.swap(k, j)
		k = j
	}
}
