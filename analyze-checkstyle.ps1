# Script to analyze checkstyle violations and list unique rules with examples and counts

Write-Host "Running checkstyle on all modules..." -ForegroundColor Yellow

# Run checkstyle and save output to file
mvn checkstyle:check 2>&1 | Out-File -FilePath checkstyle-output.txt -Encoding utf8

# Read the file and join lines
$content = Get-Content checkstyle-output.txt -Raw

# Dictionary to store rules and their examples
$rules = @{}

# Pattern to match checkstyle violations: [WARN] path:line:column: message [RuleName]
# Handle multi-line output by using regex with singleline mode
$violationPattern = '\[WARN\]\s+([A-Za-z]:[^:]+):(\d+):?(\d*):\s*([^\[]+)\[([^\]]+)\]'

$regexMatches = [regex]::Matches($content, $violationPattern)
$totalViolations = $regexMatches.Count

foreach ($match in $regexMatches) {
    $filePath = $match.Groups[1].Value.Trim()
    $lineNum = $match.Groups[2].Value
    $column = if ($match.Groups[3].Value) { $match.Groups[3].Value } else { "1" }
    $message = $match.Groups[4].Value.Trim() -replace '\s+', ' '
    $ruleName = $match.Groups[5].Value.Trim()
    
    if ($rules.ContainsKey($ruleName)) {
        # Increment the count for existing rule
        $rules[$ruleName].Count++
    } else {
        # Extract the actual line from the file for context
        $exampleCode = "(Could not read)"
        if (Test-Path $filePath) {
            $fileLines = Get-Content $filePath -ErrorAction SilentlyContinue
            if ($fileLines -and [int]$lineNum -le $fileLines.Length) {
                $exampleCode = $fileLines[[int]$lineNum - 1].Trim()
            }
        }
        
        $rules[$ruleName] = @{
            Rule = $ruleName
            Message = $message
            File = $filePath
            Line = $lineNum
            Column = $column
            ExampleCode = $exampleCode
            Count = 1
        }
    }
}

Write-Host ""
$separator = "=" * 80
Write-Host $separator -ForegroundColor Cyan
Write-Host "CHECKSTYLE VIOLATIONS SUMMARY" -ForegroundColor Cyan
Write-Host $separator -ForegroundColor Cyan
Write-Host ""
Write-Host "Total violations: $totalViolations" -ForegroundColor Red
Write-Host "Unique rules violated: $($rules.Count)" -ForegroundColor Yellow
Write-Host ""

if ($rules.Count -eq 0) {
    Write-Host "No checkstyle violations found!" -ForegroundColor Green
} else {
    # Sort rules by count (descending), then by name
    $sortedRules = $rules.Values | Sort-Object @{Expression={$_.Count}; Descending=$true}, Rule
    
    # Print summary table
    Write-Host "VIOLATIONS BY RULE (sorted by count):" -ForegroundColor White
    Write-Host $separator -ForegroundColor DarkGray
    Write-Host ("{0,-6} {1}" -f "Count", "Rule") -ForegroundColor White
    Write-Host $separator -ForegroundColor DarkGray
    
    foreach ($rule in $sortedRules) {
        $countColor = if ($rule.Count -ge 100) { "Red" } elseif ($rule.Count -ge 10) { "Yellow" } else { "Green" }
        Write-Host ("{0,5}  " -f $rule.Count) -NoNewline -ForegroundColor $countColor
        Write-Host "[$($rule.Rule)]" -ForegroundColor Magenta
    }
    
    Write-Host $separator -ForegroundColor DarkGray
    Write-Host ""
    Write-Host "DETAILED EXAMPLES:" -ForegroundColor White
    Write-Host ""
    
    foreach ($rule in $sortedRules) {
        $lineSep = "-" * 80
        Write-Host $lineSep -ForegroundColor DarkGray
        Write-Host "Rule: " -NoNewline -ForegroundColor White
        Write-Host "[$($rule.Rule)]" -NoNewline -ForegroundColor Magenta
        Write-Host " - " -NoNewline
        $countColor = if ($rule.Count -ge 100) { "Red" } elseif ($rule.Count -ge 10) { "Yellow" } else { "Green" }
        Write-Host "$($rule.Count) violation(s)" -ForegroundColor $countColor
        Write-Host "Description: " -NoNewline -ForegroundColor White
        Write-Host $rule.Message -ForegroundColor Gray
        Write-Host "Example: " -NoNewline -ForegroundColor White
        Write-Host "$($rule.File):$($rule.Line)" -ForegroundColor DarkYellow
        Write-Host "  $($rule.ExampleCode)" -ForegroundColor DarkCyan
        Write-Host ""
    }
}

Write-Host $separator -ForegroundColor Cyan

# Clean up
Remove-Item checkstyle-output.txt -ErrorAction SilentlyContinue
