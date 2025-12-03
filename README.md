# Dependency Graphs MASAQ

> **⚠️ WARNING: DRAFT WORK**
>
> This repository and its contents are currently in a **DRAFT** state. The code, data, and documentation are subject to change without notice. Use with caution.

**Status: DRAFT**

This repository contains tools to generate dependency graphs for Quranic verses using the MASAQ database.

## Overview

The `generate_dependency_svg.py` script reads Quranic text, morphology, and syntax data from `MASAQ.db` and generates Scalable Vector Graphics (SVG) visualizations of the dependency grammar.

## Usage

1.  **Prerequisites**: Python 3.8+
2.  **Run the script**:

    ```bash
    python3 generate_dependency_svg.py --surah <SURAH_NUMBER> --ayah <AYAH_NUMBER>
    ```

    Example:
    ```bash
    python3 generate_dependency_svg.py --surah 1 --ayah 1
    ```

    This will generate an SVG file in the `output_v2/` directory (created automatically).

3.  **Options**:
    *   `--surah`, `--ayah`: Specify the verse(s) to generate.
    *   `--output`: Specify a custom output path (when using `--spec`).
    *   `--debug`: Enable debug visualization (outlines, overlaps).
    *   `--verbose`: Print detailed logs.

## Data Source

This project uses the **MASAQ** dataset:
*   **Title**: MASAQ: A Multi-Modal Arabic Corpus for Quranic Analysis
*   **Source**: [Mendeley Data](https://data.mendeley.com/datasets/9yvrzxktmr/2)
*   **Credit**: Please cite the original authors when using this data.

## Contributing

This project is currently in **DRAFT** status. We welcome contributions!
*   Found a bug? Please open an Issue.
*   Want to improve the graph layout or logic? Please submit a Pull Request.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
The `MASAQ.db` file is subject to its own license terms (CC BY 4.0).
