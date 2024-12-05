#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void leer_instancias(const char *filename) {
    FILE *f;
    char linea[100];
    int start, goal;
    int *intermedios;
    int num_intermedios;
    int instancia = 0;

    f = fopen(filename, "r");
    if (f == NULL) {
        printf("Error con el archivo %s.\n", filename);
        exit(1);
    }

    while (fgets(linea, 100, f) != NULL) {
        num_intermedios = 0;	
        char *copia_linea = strdup(linea);
        start = atoi(strtok(copia_linea, " "));

        char *token = strtok(NULL, " ");
        while (token != NULL && strcmp(token, "\n") != 0) {
            num_intermedios++;
            token = strtok(NULL, " ");
        }

        num_intermedios--;
        if (num_intermedios > 0) {
            intermedios = (int *)malloc(num_intermedios * sizeof(int));
            if (intermedios == NULL) {
                printf("Error al asignar memoria.\n");
                exit(1);
            }

            strtok(linea, " ");
            for (int i = 0; i < num_intermedios; i++) {
                intermedios[i] = atoi(strtok(NULL, " "));
            }
            goal = atoi(strtok(NULL, " "));

            instancia++;
            printf("Instancia #%d:\n", instancia);
            printf("Estado inicial: %d\n", start);
            printf("Estados intermedios: ");
            for (int i = 0; i < num_intermedios; i++) {
                printf("%d ", intermedios[i]);
            }
            printf("\n");
            printf("Estado final: %d\n", goal);
            printf("\n");

            free(intermedios);
        }
        free(copia_linea);
    }

    fclose(f);
}

int main() {
    leer_instancias("NY-queries-2p.txt");
    return 0;
}

