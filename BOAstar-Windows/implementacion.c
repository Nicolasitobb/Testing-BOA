#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <unistd.h>

#define MAXNODES 4000000
#define MAXNEIGH 45
#define MAX_SOLUTIONS 1000000
#define MAX_RECYCLE  100000
#define MAX_CAMINOS 1000000 // Aumentar si es necesario

#define LARGE  1000000000
#define BASE   10000000

#define max(x,y) ( (x) > (y) ? (x) : (y) )
#define min(x,y) ( (x) < (y) ? (x) : (y) )

//********************************************** Main data structures ******************************************************
struct gnode;
typedef struct gnode gnode;

struct gnode {
  long long int id;
  unsigned h1;
  unsigned h2;
  unsigned long long int key;
  unsigned gmin;
  unsigned long heapindex;
};

struct snode;
typedef struct snode snode;

struct snode {
  int state;
  unsigned g1;
  unsigned g2;
  double key;
  unsigned long heapindex;
  snode *searchtree;
};

typedef struct {
  int *nodos; 
  int longitud; 
  unsigned g1; 
  unsigned g2; 
} Camino;


gnode* graph_node;
unsigned num_gnodes;
unsigned adjacent_table[MAXNODES][MAXNEIGH];
unsigned pred_adjacent_table[MAXNODES][MAXNEIGH];
unsigned goal, start;
gnode* start_state;
gnode* goal_state;
snode* start_node;

unsigned long long int stat_expansions = 0;
unsigned long long int stat_generated = 0;
unsigned long long int minf_solution = LARGE;

unsigned solutions[MAX_SOLUTIONS][2]; // Se mantiene para compatibilidad con el código original
unsigned nsolutions = 0;
unsigned stat_pruned = 0;
unsigned stat_created = 0;


//********************************************** Binary Heap Data Structures ******************************************************

// --------------------------   Binary Heap for Dijkstra  -----------------------------------------
#define HEAPSIZEDIJ 3000000
gnode* heap_dij[HEAPSIZEDIJ];
unsigned long int heapsize_dij = 0;
unsigned long int stat_percolations = 0;

// ---------------------------------------------------------------
void percolatedown_dij(int hole, gnode* tmp) {
  int child;

  if (heapsize_dij != 0) {
    for (; 2 * hole <= heapsize_dij; hole = child) {
      child = 2 * hole;
      if (child != heapsize_dij && heap_dij[child + 1]->key < heap_dij[child]->key)
        ++child;
      if (heap_dij[child]->key < tmp->key) {
        heap_dij[hole] = heap_dij[child];
        heap_dij[hole]->heapindex = hole;
        ++stat_percolations;
      }
      else
        break;
    } // end for
    heap_dij[hole] = tmp;
    heap_dij[hole]->heapindex = hole;
  }
}
/* --------------------------------------------------------------- */
void percolateup_dij(int hole, gnode* tmp) {
  if (heapsize_dij != 0) {
    for (; hole > 1 && tmp->key < heap_dij[hole / 2]->key; hole /= 2) {
      heap_dij[hole] = heap_dij[hole / 2];
      heap_dij[hole]->heapindex = hole;
      ++stat_percolations;
    }
    heap_dij[hole] = tmp;
    heap_dij[hole]->heapindex = hole;
  }
}
/* --------------------------------------------------------------- */
void percolateupordown_dij(int hole, gnode* tmp) {
  if (heapsize_dij != 0) {
    if (hole > 1 && heap_dij[hole / 2]->key > tmp->key)
      percolateup_dij(hole, tmp);
    else
      percolatedown_dij(hole, tmp);
  }
}
/* --------------------------------------------------------------- */
void insertheap_dij(gnode* thiscell) {

  if (thiscell->heapindex == 0)
    percolateup_dij(++heapsize_dij, thiscell);
  else
    percolateupordown_dij(thiscell->heapindex, heap_dij[thiscell->heapindex]);
}
/* --------------------------------------------------------------- */
void deleteheap_dij(gnode* thiscell) {
  if (thiscell->heapindex != 0) {
    percolateupordown_dij(thiscell->heapindex, heap_dij[heapsize_dij--]);
    thiscell->heapindex = 0;
  }
}
/* --------------------------------------------------------------- */
gnode* topheap_dij() {
  if (heapsize_dij == 0)
    return NULL;
  return heap_dij[1];
}
/* --------------------------------------------------------------- */
void emptyheap_dij() {
  int i;

  for (i = 1; i <= heapsize_dij; ++i)
    heap_dij[i]->heapindex = 0;
  heapsize_dij = 0;
}

/* --------------------------------------------------------------- */
gnode* popheap_dij() {
  gnode* thiscell;

  if (heapsize_dij == 0)
    return NULL;
  thiscell = heap_dij[1];
  thiscell->heapindex = 0;
  percolatedown_dij(1, heap_dij[heapsize_dij--]);
  return thiscell;
}

int sizeheap_dij() {
  return heapsize_dij;
}

gnode* posheap_dij(int i) {
  return heap_dij[i];
}

// --------------------------   Binary Heap for BOA*  -----------------------------------------
#define HEAPSIZE 40000000
snode* heap[HEAPSIZE];
unsigned long int heapsize = 0;

// ---------------------------------------------------------------
void percolatedown(int hole, snode* tmp) {
  int child;

  if (heapsize != 0) {
    for (; 2 * hole <= heapsize; hole = child) {
      child = 2 * hole;
      if (child != heapsize && heap[child + 1]->key < heap[child]->key)
        ++child;
      if (heap[child]->key < tmp->key) {
        heap[hole] = heap[child];
        heap[hole]->heapindex = hole;
        ++stat_percolations;
      }
      else
        break;
    } // end for
    heap[hole] = tmp;
    heap[hole]->heapindex = hole;
  }
}
/* --------------------------------------------------------------- */
void percolateup(int hole, snode* tmp) {
  if (heapsize != 0) {
    for (; hole > 1 && tmp->key < heap[hole / 2]->key; hole /= 2) {
      heap[hole] = heap[hole / 2];
      heap[hole]->heapindex = hole;
      ++stat_percolations;
    }
    heap[hole] = tmp;
    heap[hole]->heapindex = hole;
  }
}
/* --------------------------------------------------------------- */
void percolateupordown(int hole, snode* tmp) {
  if (heapsize != 0) {
    if (hole > 1 && heap[hole / 2]->key > tmp->key)
      percolateup(hole, tmp);
    else
      percolatedown(hole, tmp);
  }
}
/* --------------------------------------------------------------- */
void insertheap(snode* thiscell) {
  if (thiscell->heapindex == 0)
    percolateup(++heapsize, thiscell);
  else
    percolateupordown(thiscell->heapindex, heap[thiscell->heapindex]);
}
/* --------------------------------------------------------------- */
void deleteheap(snode* thiscell) {
  if (thiscell->heapindex != 0) {
    percolateupordown(thiscell->heapindex, heap[heapsize--]);
    thiscell->heapindex = 0;
  }
}
/* --------------------------------------------------------------- */
snode* topheap() {
  if (heapsize == 0)
    return NULL;
  return heap[1];
}
/* --------------------------------------------------------------- */
void emptyheap() {
  int i;

  for (i = 1; i <= heapsize; ++i)
    heap[i]->heapindex = 0;
  heapsize = 0;
}

/* --------------------------------------------------------------- */
snode* popheap() {
  snode* thiscell;

  if (heapsize == 0)
    return NULL;
  thiscell = heap[1];
  thiscell->heapindex = 0;
  percolatedown(1, heap[heapsize--]);
  return thiscell;
}

int sizeheap() {
  return heapsize;
}

long int opensize() {
  return heapsize_dij;
}
snode* posheap(int i) {
  return heap[i];
}
// --------------------------    Binary Heap end --------------------------------------------




//********************************************** Reading the file ******************************************************

void read_adjacent_table(const char* filename) {
	FILE* f;
	int i, ori, dest, dist, t;
	f = fopen(filename, "r");
	int num_arcs = 0;
	if (f == NULL) 	{
		printf("Cannot open file %s.\n", filename);
		exit(1);
	}
	fscanf(f, "%d %d", &num_gnodes, &num_arcs);
	fscanf(f, "\n");
//	printf("%d %d", num_gnodes, num_arcs);
	for (i = 0; i < num_gnodes; i++)
		adjacent_table[i][0] = 0;

	for (i = 0; i < num_arcs; i++) {
		fscanf(f, "%d %d %d %d\n", &ori, &dest, &dist, &t);
	//	printf("%d %d %d %d\n", ori, dest, dist, t);
		adjacent_table[ori - 1][0]++;
		adjacent_table[ori - 1][adjacent_table[ori - 1][0] * 3 - 2] = dest - 1;
		adjacent_table[ori - 1][adjacent_table[ori - 1][0] * 3 - 1] = dist;
		adjacent_table[ori - 1][adjacent_table[ori - 1][0] * 3] = t;

		pred_adjacent_table[dest - 1][0]++;
		pred_adjacent_table[dest - 1][pred_adjacent_table[dest - 1][0] * 3 - 2] = ori - 1;
		pred_adjacent_table[dest - 1][pred_adjacent_table[dest - 1][0] * 3 - 1] = dist;
		pred_adjacent_table[dest - 1][pred_adjacent_table[dest - 1][0] * 3] = t;
	}
	fclose(f);
}

void new_graph() {
	int y;
	if (graph_node == NULL) {
		graph_node = (gnode*) calloc(num_gnodes, sizeof(gnode));
		for (y = 0; y < num_gnodes; ++y) 		{
			graph_node[y].id = y;
			graph_node[y].gmin = LARGE;
			graph_node[y].h1 = LARGE;
			graph_node[y].h2 = LARGE;
		}
	}
}



//********************************************** BOA* ******************************************************

void initialize_parameters() {
    start_state = &graph_node[start];
    goal_state = &graph_node[goal];
    stat_percolations = 0;
    minf_solution = LARGE; // Reiniciar minf_solution
    nsolutions = 0; // Reiniciar nsolutions
}

int backward_dijkstra(int dim) {
    int i;
	for (i = 0; i < num_gnodes; ++i)
        graph_node[i].key = LARGE;
    emptyheap_dij();
    goal_state->key = 0;
    insertheap_dij(goal_state);

    while (topheap_dij() != NULL) {
        gnode* n;
        gnode* pred;
        short d;
        n = popheap_dij();
        if (dim == 1)
            n->h1 = n->key;
        else
            n->h2 = n->key;
        ++stat_expansions;
        for (d = 1; d < pred_adjacent_table[n->id][0] * 3; d += 3) {
            pred = &graph_node[pred_adjacent_table[n->id][d]];
            int new_weight = n->key + pred_adjacent_table[n->id][d + dim];
            if (pred->key > new_weight) {
                pred->key = new_weight;
                insertheap_dij(pred);
            }
        }
    }
    return 1;
}

snode* new_node() {
    snode* state = (snode*)malloc(sizeof(snode));
    state->heapindex = 0;
    return state;
}


Camino* boastar() { 
  snode* recycled_nodes[MAX_RECYCLE];
  int next_recycled = 0;
  nsolutions = 0;
  stat_pruned = 0;
  emptyheap();

  start_node = new_node();
  ++stat_created;
  start_node->state = start;
  start_node->g1 = 0;
  start_node->g2 = 0;
  start_node->key = 0;
  start_node->searchtree = NULL;
  insertheap(start_node);

  stat_expansions = 0;
  while (topheap() != NULL) {
    snode* n = popheap(); 
    short d;

    if (n->g2 >= graph_node[n->state].gmin || n->g2 + graph_node[n->state].h2 >= minf_solution) {
      stat_pruned++;
      if (next_recycled < MAX_RECYCLE) {
        recycled_nodes[next_recycled++] = n;
      }
      continue;
    }

    graph_node[n->state].gmin = n->g2;

    if (n->state == goal) {
      // Guardar la solución en el arreglo solutions (para compatibilidad)
      solutions[nsolutions][0] = n->g1;
      solutions[nsolutions][1] = n->g2;

      nsolutions++;
      if (nsolutions > MAX_SOLUTIONS) {
        printf("Maximum number of solutions reached, increase MAX_SOLUTIONS!\n");
        exit(1);
      }
      if (minf_solution > n->g2) {
        minf_solution = n->g2;
      }
      continue;
    }

    ++stat_expansions;

    for (d = 1; d < adjacent_table[n->state][0] * 3; d += 3) {
      snode* succ;
      double newk1, newk2, newkey;
      unsigned nsucc = adjacent_table[n->state][d];
      unsigned cost1 = adjacent_table[n->state][d + 1];
      unsigned cost2 = adjacent_table[n->state][d + 2];

      unsigned newg1 = n->g1 + cost1;
      unsigned newg2 = n->g2 + cost2;
      unsigned h1 = graph_node[nsucc].h1;
      unsigned h2 = graph_node[nsucc].h2;

      if (newg2 >= graph_node[nsucc].gmin || newg2 + h2 >= minf_solution)
        continue;

      newk1 = newg1 + h1;
      newk2 = newg2 + h2;

      if (next_recycled > 0) { 
        succ = recycled_nodes[--next_recycled];
      }
      else {
        succ = new_node();
        ++stat_created;
      }

      succ->state = nsucc;
      stat_generated++;

      newkey = newk1 * (double)BASE + newk2;
      succ->searchtree = n;
      succ->g1 = newg1;
      succ->g2 = newg2;
      succ->key = newkey;
      insertheap(succ);
    }
  }

  // Crear un arreglo de caminos (Camino) a partir de las soluciones encontradas
  Camino* caminos_soluciones = (Camino*)malloc(nsolutions * sizeof(Camino));
  for (int i = 0; i < nsolutions; i++) {
    caminos_soluciones[i].g1 = solutions[i][0];
    caminos_soluciones[i].g2 = solutions[i][1];

    // Reconstruir el camino (similar al código anterior)
    int longitud_camino = 0;
    snode* nodo_actual = popheap(); // Obtener la solución del heap (en orden inverso)
    while (nodo_actual != NULL) {
      longitud_camino++;
      nodo_actual = nodo_actual->searchtree;
    }

    caminos_soluciones[i].nodos = (int*)malloc(longitud_camino * sizeof(int));
    caminos_soluciones[i].longitud = longitud_camino;

    nodo_actual = popheap(); // Obtener la solución del heap nuevamente
    for (int j = longitud_camino - 1; j >= 0; j--) {
      caminos_soluciones[i].nodos[j] = nodo_actual->state;
      nodo_actual = nodo_actual->searchtree;
    }
  }

  // Retornar el arreglo de caminos
  return caminos_soluciones;
}


/* ------------------------------------------------------------------------------*/
void call_boastar(int s, int g) {
    float runtime;
    struct timeval tstart, tend;
    unsigned long long min_cost;
    unsigned long long min_time;

    initialize_parameters();

    gettimeofday(&tstart, NULL);

    //Dijkstra h1
    if (backward_dijkstra(1))
        min_cost = start_state->h1;

    //Dijkstra h2
    if (backward_dijkstra(2))
        min_time = start_state->h2;
        
    
	//BOA*
    boastar();

		
    gettimeofday(&tend, NULL);
    runtime = 1.0 * (tend.tv_sec - tstart.tv_sec) + 1.0 * (tend.tv_usec - tstart.tv_usec) / 1000000.0;
    //		printf("nsolutions:%d Runtime(ms):%f Generated: %llu statexpanded1:%llu\n", nsolutions, time_astar_first1*1000, stat_generated, stat_expansions);
    printf("%lld;%lld;%d;%f;%llu;%llu;%lu;%llu\n",
        start_state->id + 1,
        goal_state->id + 1,
        nsolutions,
        runtime * 1000,
        stat_generated,
        stat_expansions,
        stat_created,
        stat_percolations);
}

//********************************************** BCBiMDS ******************************************************

// Función para combinar dos fronteras de Pareto
Camino* combinar_fronteras(Camino* frontera1, int num_soluciones1, Camino* frontera2, int num_soluciones2, int* num_soluciones_global) {
  
  *num_soluciones_global = num_soluciones1 * num_soluciones2; 
  Camino* frontera_combinada = (Camino*)malloc(*num_soluciones_global * sizeof(Camino));

  int indice = 0;
  for (int i = 0; i < num_soluciones1; i++) {
    for (int j = 0; j < num_soluciones2; j++) {
      // Combinar caminos (concatenar nodos)
      int nueva_longitud = frontera1[i].longitud + frontera2[j].longitud - 1; // -1 porque el último nodo del primer camino es el mismo que el primero del segundo
      frontera_combinada[indice].nodos = (int*)malloc(nueva_longitud * sizeof(int));
      frontera_combinada[indice].longitud = nueva_longitud;
      memcpy(frontera_combinada[indice].nodos, frontera1[i].nodos, frontera1[i].longitud * sizeof(int));
      memcpy(frontera_combinada[indice].nodos + frontera1[i].longitud - 1, frontera2[j].nodos + 1, (frontera2[j].longitud - 1) * sizeof(int)); 

      // Calcular los costos
      frontera_combinada[indice].g1 = frontera1[i].g1 + frontera2[j].g1;
      frontera_combinada[indice].g2 = frontera1[i].g2 + frontera2[j].g2;

      indice++;
    }
  }

  // Filtrar las soluciones no dominadas
  int num_no_dominadas = 0;
  for (int i = 0; i < *num_soluciones_global; i++) {
    int es_dominada = 0;
    for (int j = 0; j < *num_soluciones_global; j++) {
      if (i != j && 
          frontera_combinada[j].g1 <= frontera_combinada[i].g1 && 
          frontera_combinada[j].g2 <= frontera_combinada[i].g2 && 
          (frontera_combinada[j].g1 < frontera_combinada[i].g1 || 
           frontera_combinada[j].g2 < frontera_combinada[i].g2)) {
        es_dominada = 1;
        break;
      }
    }
    if (!es_dominada) {
      // Mover la solución no dominada al principio del arreglo
      if (i != num_no_dominadas) {
        Camino temp = frontera_combinada[num_no_dominadas];
        frontera_combinada[num_no_dominadas] = frontera_combinada[i];
        frontera_combinada[i] = temp;
      }
      num_no_dominadas++;
    }
  }

  *num_soluciones_global = num_no_dominadas;

  return frontera_combinada;
}


// Función para resolver el BCBiMDS
void BCBiMDS(int start, int* intermedios, int num_intermedios, int goal) {
  Camino* frontera_global = NULL;
  int num_soluciones_global = 0;
  int estado_actual = start;

  struct timeval tstart, tend;
  gettimeofday(&tstart, NULL);

  for (int i = 0; i <= num_intermedios; i++) {
    int destino = (i < num_intermedios) ? intermedios[i] : goal; 

    // Llamar a BOA*
    goal = destino; // Actualizar el objetivo global para BOA*
    Camino* frontera_local = boastar(); 
    int num_soluciones_local = nsolutions; 

    // Combinar fronteras
    frontera_global = combinar_fronteras(frontera_global, num_soluciones_global, frontera_local, num_soluciones_local, &num_soluciones_global);

    estado_actual = destino;
  }

  gettimeofday(&tend, NULL);
  float runtime = 1.0 * (tend.tv_sec - tstart.tv_sec) + 1.0 * (tend.tv_usec - tstart.tv_usec) / 1000000.0;

  // Imprimir resultados en el formato requerido
  printf("#instancia;%d;%f;%llu;%llu\n", 
         num_soluciones_global, // número de soluciones
         runtime * 1000, // tiempo de ejecución 
         stat_expansions, // #nodos expandidos
         stat_generated); // #nodos generados

  // Liberar memoria (frontera_global y sus caminos)
  for (int i = 0; i < num_soluciones_global; i++) {
    free(frontera_global[i].nodos);
  }
  free(frontera_global);
}


//********************************************** Main function ******************************************************

void leer_instancias(const char *filename) {
  // ... (código de la función leer_instancias - igual que el anterior) ...
}

/*----------------------------------------------------------------------------------*/
int main() {
  // ... (código de la función main - igual que el anterior) ...
}
