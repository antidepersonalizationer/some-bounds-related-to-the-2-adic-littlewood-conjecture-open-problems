param([string]$DependencyPackages = '')
& (Join-Path $PSScriptRoot 'Check-Project.ps1') -DependencyPackages $DependencyPackages
