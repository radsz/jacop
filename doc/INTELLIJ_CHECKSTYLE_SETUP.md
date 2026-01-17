# IntelliJ IDEA Checkstyle Auto-Fix Setup Guide

This guide helps you configure IntelliJ IDEA to automatically fix Checkstyle violations.

## Step 1: Install CheckStyle-IDEA Plugin

1. Open IntelliJ IDEA
2. Go to **File → Settings** (or **IntelliJ IDEA → Preferences** on Mac)
3. Navigate to **Plugins**
4. Search for "**CheckStyle-IDEA**"
5. Click **Install** and restart IDE if prompted

## Step 2: Configure Checkstyle

1. Go to **Settings → Tools → Checkstyle**
2. Click the **"+"** button to add a new configuration
3. Configure:
   - **Description**: `JaCoP Checkstyle`
   - **Checkstyle version**: Use `13.0.0` (or bundled version)
   - **Configuration file**: Browse to `jacop/doc/checkstyle.xml`
   - Check **"Active"** checkbox
4. Click **OK**

## Step 3: Enable Checkstyle Inspections

1. Go to **Settings → Editor → Inspections**
2. Search for "**Checkstyle**"
3. Enable **"CheckStyle"** inspection
4. Optionally enable **"CheckStyle violations"** for real-time highlighting

## Step 4: Import Checkstyle as Code Style

1. Go to **Settings → Editor → Code Style → Java**
2. Click the **gear icon** (⚙️) next to the scheme dropdown
3. Select **"Import Scheme → Checkstyle Configuration"**
4. Browse to `jacop/doc/checkstyle.xml`
5. This will map Checkstyle rules to IntelliJ's formatter

## Step 5: Enable Actions on Save

1. Go to **Settings → Tools → Actions on Save**
2. Enable:
   - ✅ **Reformat code**
   - ✅ **Optimize imports**
   - ✅ **Run Checkstyle** (if available)

## Step 6: Enable Structural Fix Inspections

1. Go to **Settings → Editor → Inspections**
2. Search for and enable:
   - **"Control flow statement without braces"** (fixes NeedBraces violations)
   - **"Missing Javadoc"** (helps with MissingJavadocMethod)
3. These inspections can auto-fix many structural issues

## Step 7: Bulk Fix All Violations

### Option A: Fix All in Project
1. Go to **Code → Inspect Code...**
2. Select scope: **"Whole project"** or **"Module 'jacop'"`
3. Click **OK**
4. Wait for inspection to complete
5. In the inspection results:
   - Right-click on a violation type → **"Fix all 'X' problems in file"** or **"...in project"**
   - Or use **Alt+Enter** on each violation and select **"Fix all"**

### Option B: Fix File by File
1. Open a file with violations
2. Press **Alt+Enter** on any violation
3. Select the fix option (e.g., "Add braces", "Add Javadoc")
4. For bulk fixes in file: Right-click → **"Fix all 'X' problems in file"**

## What Gets Auto-Fixed

✅ **Can be auto-fixed:**
- NeedBraces violations (adding braces to if/else/for/while)
- Formatting issues (indentation, spacing, line breaks)
- Import organization
- Some Javadoc issues (via inspections)

❌ **May need manual intervention:**
- Complex Javadoc requirements
- Custom Checkstyle rules without IntelliJ equivalents
- Some naming convention violations

## Tips

- Use **Ctrl+Alt+L** (or **Cmd+Option+L** on Mac) to reformat code manually
- Use **Ctrl+Alt+O** (or **Cmd+Option+O** on Mac) to optimize imports
- Checkstyle violations will show as warnings/errors in the editor
- Use **Alt+Enter** for quick fixes on any violation

## Troubleshooting

- If Checkstyle doesn't run: Check that the configuration is "Active" in Settings → Tools → Checkstyle
- If auto-fix doesn't work: Make sure the corresponding inspection is enabled in Settings → Editor → Inspections
- If formatting doesn't match: Re-import the Checkstyle config as Code Style scheme
